/***
 SnoKoder: a nice sounding vocoder for JACK
 Version 1.4
 --

 To compile this:
    gcc snokoder.c -lpthread -lm -ljack -lfftw3 -lcurses -lasound -ffast-math -O3 -o snokoder


 Copyright 2011, Elie Goldman Smith

 This program is FREE SOFTWARE: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.

 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <https://www.gnu.org/licenses/>.
***/

// 
// TODO in the next version: implement stereo output
//                           - fft_noteL[] and fft_notewaveL[], etc
// TODO in the next version: implement noise mode and square mode
//                           - where will it go in the UI?
//                             - remove the thin bands option?
#include <alsa/asoundlib.h>
#include <ctype.h>
#include <curses.h>
#include <fftw3.h>
#include <jack/jack.h>
#include <math.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/times.h>
#include <unistd.h>

// basic tone detail parameters
#define FFT_N 512 // spectrum analyzer window size: MUST BE A POWER OF TWO

// other audio processing parameters
#define COMPRESSOR_ATTACK 4096 // how slow the compressor changes volume
#define COMPRESSOR_RATIO 2       // the decibel ratio of the compressor
#define ECHO_MAX 65536 // max delay time in samples: MUST BE A POWER OF TWO
#define GATE_SMOOTHNESS 512 // used for noise gate dynamics in non-vocoder
#define LIMITER_RELEASE 1024 // how slow the limiter recovers from loud peaks

// vocoder note keying modes
#define NOTES_SINGLE 1 // only sing one note at a time
#define NOTES_DOUBLE 2 // two notes - one high one low
#define NOTES_CHORDS 3 // press keys together to form chords

// voice-through modes
#define THRU_NONE     0 // vocoder only, or natural voice if no notes
#define THRU_REALFAKE 1 // mix your natural voice with the vocoded voice
#define THRU_AUTOTUNE 2 // (not yet implemented) add an auto-tuned note to the vocoder

// text display parameters
#define INFO_X 29
#define INFO_Y 11
#define NOTES_X 4
#define NOTES_Y 7

// makes code look cleaner
#define STATE(b)   ((b)?"ON":"OFF")
typedef jack_default_audio_sample_t sample_t;

snd_seq_t* seq_handle; // ALSA midi handle
jack_client_t* client;    // 
jack_port_t* midi_port;   // JACK
jack_port_t* input_port;  // globals
jack_port_t* output_port; // 

sample_t v_nexttime[FFT_N]; // tail end of vocoder, for next jack call
double v_spectrum[FFT_N/2+1]; // the vocal spectrum collected
double v_noise[FFT_N/2+1]; // the background mic noise
double v_filt[FFT_N/2+1]; // power gain of each frequency band

double fft_wave1[FFT_N]; // the first window of data for spectrum analyzer
double fft_wave2[FFT_N]; // the second window, 50% overlap of first
double fft_freq1[FFT_N]; // the FFT of wave1
double fft_freq2[FFT_N]; // the FFT of wave2
double fft_window[FFT_N]; // the window function (Hanning)
double fft_notewave[FFT_N]; // holds the waveform of a vocoded note
double fft_note[FFT_N]; // holds the harmonic info of a vocoded note
sample_t echobuf[ECHO_MAX]; // the buffer for echoes and delays
sample_t noise_level = 0; // the noise floor in non-vocoder mode

int offset_key = 0; // determines which musical scale we're using
int notes_mode = NOTES_CHORDS; // which way to control the notes
static const char* NOTES_MODE_NAMES[] = // descriptions of the notes modes
{ "----\n","single note only\n","bassline/melody\n","freeform chords\n" };

static const char* THRU_MODE_NAMES[] = // descriptions of the vocal mix modes
{ "single sound\n","50/50 harmony\n","auto-tuning\n" };
int thru_mode = THRU_NONE;

int note_C; // which of the 12 vocoder notes is C
int midi_LOW; // the MIDI number equivalent to the lowest vocoder note
char *note_name[12]; // properly-aligned name of each of the 12 notes
static const char *FIXED_NOTE_NAMES[12] = // the unaligned note names
	{"A","Bb","B","C","Db","D","Eb","E","F","Gb","G","Ab"};

struct Vocoder_Note_Struct {
	int oct0; // volume of
	int oct1; // the note
	int oct2; // in each
	int oct3; // octave
	fftw_plan plan; // the iFFT plan
	int N; // number of samples in the iFFT
	int i; // keeps track of the position in the waveform
	double* phases; // the phase of each harmonic. they are randomized
	int use_in_autotune; // allow note in auto-tune mode
} notes[12];

fftw_plan plan_forward1; // forward FFT for first (aligned) window
fftw_plan plan_forward2; // forward FFT for second (offset) window
fftw_plan plan_backward1; // backward FFT for first (aligned) window
fftw_plan plan_backward2; // backward FFT for second (offset) window

int using_echo = 0;
int clear_echo = 0;
int clear_noise = 0;
int input_gain_dB = 6;
int plans_are_made = 0;
int collecting_noise = 0;
int using_thin_bands = 1;
int muting_everything = 0;
int recording_to_file = 0;
int compressor_thresh = -15;
long echo_time = 7654;
long sample_rate = -1;
double formant_shift = 1;
WINDOW* curses_window = NULL;


// all AUDIO INPUT AND OUTPUT code in this next function:
int My_Process (jack_nframes_t nframes, void *arg)
{
	// get the pointers to the input and output audio buffers
	sample_t *out =(sample_t *) jack_port_get_buffer(output_port, nframes);
	sample_t *input = (sample_t *) jack_port_get_buffer (input_port, nframes);
	int i;

	// handle any requests to clear data
	if (clear_echo) memset(echobuf,0,sizeof(echobuf));
	if (clear_noise) {
		memset(v_noise,0,sizeof(v_noise));
		noise_level = 0;
	}

	// the *in buffer will be the "prepared" input (i.e. DC offset removed)
	static sample_t *in = NULL;
	static jack_nframes_t old_nframes = 0;
	if (nframes != old_nframes)
	{
		if (in != NULL) free(in);
		in = malloc(nframes*sizeof(sample_t));
		old_nframes = nframes;
		// TODO: research: do I really need to error-check on every single malloc? srsly?
		// XXX: should I do this malloc outside this function?
		//      - call it in when setting up JACK
		//      - free it when the program exits
		//      - keep it as a global variable and then alias it to *in locally
		//      - but what if 'nframes' changes from one My_Process() call to another?
		//        - could that ever happen?
		//      - it's only 2 KB. could this ever really take more than a millisecond?
	}
	// prepare the input
	static sample_t DCoffset=0;
	for (i=0; i<nframes; i++) {
		DCoffset += (input[i] - DCoffset) / 32;
		in[i] = input[i] - DCoffset;
	}

	// prepare the output (start with silence)
	memset( out, 0, sizeof(sample_t)*nframes );
	if (muting_everything) return 0; // mute

	// debugging: test everything using white noise
    // for (i=0; i<nframes; i++) in[i] = 0.1f*rand()/RAND_MAX - 0.05f;

	// check if there are notes to be vocoded
	for (i=0; i<12; i++)
		if (notes[i].oct0 > 0 ||
		    notes[i].oct1 > 0 ||
		    notes[i].oct2 > 0 ||
		    notes[i].oct3 > 0) break;
	int thistime_vocoder = (i < 12) || collecting_noise ;
	int thistime_natural = !thistime_vocoder || thru_mode==THRU_REALFAKE
	                                         || collecting_noise ;
	static int lasttime_vocoder=0;
	static int lasttime_natural=0;

	// NON-VOCODER MODE:
	if (thistime_natural || lasttime_natural)
	{
		// just use your natural voice
		memcpy(out, in, sizeof(sample_t)*nframes);

		// do some noise removal
		static sample_t power = 0;
		if (noise_level > 0 || collecting_noise)
		{
			sample_t gate = noise_level*2;
			for (i=0; i<nframes; i++)
			{
				power += (out[i]*out[i]-power) * (1.0f/GATE_SMOOTHNESS);
				if (power < noise_level) out[i] = 0; // mute noise
				else if (power < gate) // smooth fading in/out
					out[i] *= (power-noise_level)/noise_level;
			}
			if (collecting_noise && power > noise_level) noise_level = power;
		}

		if (thistime_natural && !lasttime_natural) // need to fade in
			for (i=0; i<FFT_N; i++) out[i] *= (sample_t)i/FFT_N;
		else if(lasttime_natural && !thistime_natural) { // need to fade out
			for (i=0; i<FFT_N; i++) out[i] *= (sample_t)(FFT_N-i)/FFT_N;
			for (; i<nframes; i++) out[i] = 0;
			power = 0;
		}
	}

	// VOCODER MODE:
	if (plans_are_made && (thistime_vocoder||lasttime_vocoder)) {

		// first make sure that processing can be done
		if (nframes == 0 || nframes/FFT_N*FFT_N != nframes)
		{ fprintf(stderr,"need a multiple of %d frames/period\n",FFT_N);
		  fprintf(stderr,"please restart JACK with the new setting\n");
		  return 1; }

		// get the leftover output from last jack function call
		for (i=0; i<FFT_N; i++) {
			out[i] += v_nexttime[i];
			v_nexttime[i] = 0; // clear it for this time
		}

		// if switching out of vocoder mode, then that's all we need
		if (lasttime_vocoder && !thistime_vocoder) goto FinalProcessing;

		// break the input into sections and process them all
		int section;
		for (section=0; section < nframes; section += FFT_N)
		{
			// get the aligned window (starts/ends at multiples of FFT_N)
			for (i=0; i<FFT_N; i++)
				fft_wave1[i] = in[i+section]*fft_window[i];

			// get the offset window (50% overlap)
			if (section == 0)
			{	// just the second half (first half from last time)
				for (i=FFT_N/2; i<FFT_N; i++)
					fft_wave2[i] = in[i-FFT_N/2]*fft_window[i];
			} else
			{	// if it's all within the samples
				for (i=0; i<FFT_N; i++)
					fft_wave2[i] = in[i+section-FFT_N/2]*fft_window[i];
			}

			// analyze the two overlapping windows
			fftw_execute(plan_forward1);
			fftw_execute(plan_forward2);

			// if we just came from non-vocoder mode, freq2 has glitches
			if (thistime_vocoder && !lasttime_vocoder && section == 0)
				memset(fft_freq2,0,sizeof(fft_freq2));

			// get the average power spectrum (store it in v_spectrum)
			// keep everything the square of the amplitude it should be
			for (i=1; i<=FFT_N/2; i++) v_spectrum[i] =
				fft_freq1[FFT_N-i] * fft_freq1[FFT_N-i]
				 + fft_freq1[i] * fft_freq1[i]
				+ fft_freq2[FFT_N-i] * fft_freq2[FFT_N-i]
				 + fft_freq2[i] * fft_freq2[i];
			v_spectrum[0] = 0;       // don't want any DC
			v_spectrum[FFT_N/2] /= 2; // correct highest frequency
			v_spectrum[FFT_N/2+1] = 0; // need this zero for interpolation

			// do some noise removal, either collecting or removing
			if (collecting_noise) {
				for (i=1; i<=FFT_N/2; i++)
				{
					if (v_noise[i] < v_spectrum[i]*2)
						v_noise[i] = v_spectrum[i]*2;
					v_spectrum[i] *= v_filt[i];
				}
			}
			else {
				for (i=1; i<=FFT_N/2; i++)
				{
					v_spectrum[i] -= v_noise[i];
					if (v_spectrum[i] < 0) v_spectrum[i] = 0;
					else v_spectrum[i] *= v_filt[i];
				}
			}

			// figure out how loud things will get, so it can be corrected
			double volume_fix = 0;
			if (using_thin_bands) {
				for (i=0; i<12; i++) {
					if (notes[i].oct0 > 0) volume_fix += notes[i].N/1.0/FFT_N;
					if (notes[i].oct1 > 0) volume_fix += notes[i].N/2.0/FFT_N;
					if (notes[i].oct2 > 0) volume_fix += notes[i].N/4.0/FFT_N;
					if (notes[i].oct3 > 0) volume_fix += notes[i].N/8.0/FFT_N;
				}
			} else {
				for (i=0; i<12; i++) {
					if (notes[i].oct0 > 0) volume_fix++;
					if (notes[i].oct1 > 0) volume_fix++;
					if (notes[i].oct2 > 0) volume_fix++;
					if (notes[i].oct3 > 0) volume_fix++;
				}
			}
			volume_fix = sqrt(1.0 / volume_fix);

			// go through the notes and start vocoding
			int note;
			for (note=0; note<12; note++)
			{
				if (notes[note].oct0 == 0
				 && notes[note].oct1 == 0
				 && notes[note].oct2 == 0
				 && notes[note].oct3 == 0) continue;

				int nI = notes[note].i; // makes code cleaner
				int nN = notes[note].N; // and faster
				int nN2 = nN/2 + nN%2;

				memset( fft_note, 0, nN*sizeof(double) );

				// transfer the spectral information
				// linear interpolation of harmonics

				if (using_thin_bands) // thin bandwidth - clearer vowels
				{
					double scale = (double)FFT_N/nN/formant_shift;
					if (notes[note].oct0 > 0)
						for (i=1; i<nN2; i+=1)
						{	int point = i*scale;
							if (point > FFT_N/2) break; // ends here
							double coeff = (double)i*scale - point;
							fft_note[i] += v_spectrum[point]*(1-coeff)
							             + v_spectrum[point+1]*coeff; }
					if (notes[note].oct1 > 0)
						for (i=2; i<nN2; i+=2)
						{	int point = i*scale;
							if (point > FFT_N/2) break; // ends here
							double coeff = (double)i*scale - point;
							fft_note[i] += v_spectrum[point]*(1-coeff)
							             + v_spectrum[point+1]*coeff; }
					if (notes[note].oct2 > 0)
						for (i=4; i<nN2; i+=4)
						{	int point = i*scale;
							if (point > FFT_N/2) break; // ends here
							double coeff = (double)i*scale - point;
							fft_note[i] += v_spectrum[point]*(1-coeff)
							             + v_spectrum[point+1]*coeff; }
					if (notes[note].oct3 > 0)
						for (i=8; i<nN2; i+=8) {
							int point = i*scale;
							if (point > FFT_N/2) break; // ends here
							double coeff = (double)i*scale - point;
							fft_note[i] += v_spectrum[point]*(1-coeff)
							             + v_spectrum[point+1]*coeff; }
				}
				else // wide bandwidth mode - less picky about vocals
				{
					if (notes[note].oct0 > 0)
					{
						double scale = formant_shift*nN/FFT_N;
						int end = FFT_N/2;
						if (formant_shift > 1) end /= formant_shift;

						for (i=1; i<end; i++)
						{
							int point = i*scale; // roundabout way of rounding
							double coeff = i*scale - point;
							fft_note[point] += v_spectrum[i] * (1-coeff);
							fft_note[(point+1)] += v_spectrum[i] * coeff;
						}
					}
					if (notes[note].oct1 > 0)
					{
						double scale = formant_shift*nN/FFT_N/2;
						int end = FFT_N/2;
						if (formant_shift > 1) end /= formant_shift;

						for (i=1; i<end; i++)
						{
							int point = i*scale;
							double coeff = i*scale - point;
							fft_note[point*2] += v_spectrum[i] * (1-coeff);
							fft_note[(point+1)*2] += v_spectrum[i] * coeff;
						}
					}
					if (notes[note].oct2 > 0)
					{
						double scale = formant_shift*nN/FFT_N/4;
						int end = FFT_N/2;
						if (formant_shift > 1) end /= formant_shift;

						for (i=1; i<end; i++)
						{
							int point = i*scale;
							double coeff = i*scale - point;
							fft_note[point*4] += v_spectrum[i] * (1-coeff);
							fft_note[(point+1)*4] += v_spectrum[i] * coeff;
						}
					}
					if (notes[note].oct3 > 0)
					{
						double scale = formant_shift*nN/FFT_N/8;
						int end = FFT_N/2;
						if (formant_shift > 1) end /= formant_shift;

						for (i=1; i<end; i++)
						{
							int point = i*scale;
							double coeff = i*scale - point;
							fft_note[point*8] += v_spectrum[i] * (1-coeff);
							fft_note[(point+1)*8] += v_spectrum[i] * coeff;
						}
					}
				}				

				// correct all the amplitudes (un-square, normalize, and phase)
				fft_note[0] = 0; fft_note[nN2] = 0;
				for (i=1; i<nN2; i++) {
				  if (fft_note[i] > 0) {
					double amp = sqrt(fft_note[i]) * volume_fix/FFT_N/FFT_N;
					double phase = notes[note].phases[i];
					phase += 0.0625*rand()/RAND_MAX-0.03125;
					if (phase >= 4.0) phase -= M_PI*2;
					if (phase <= -4.0) phase += M_PI*2;
					fft_note[i] = amp * cos(phase);
					fft_note[nN-i] = amp * sin(phase);
					notes[note].phases[i] = phase; // gradual random shift
				  }
				  else fft_note[nN-i] = 0;
				}

				// finally put it all into a waveform
				fftw_execute(notes[note].plan);

				// add the note fading in
				for (i=0; i<FFT_N; i++) {
					nI++; nI %= nN;
					out[i+section] += fft_notewave[nI] * i;
				}
				// add the note fading out
				if (section < nframes-FFT_N) {
					for (i=0; i<FFT_N; i++) { // this time
						nI++; nI %= nN;
						out[i+section+FFT_N] += fft_notewave[nI] * (FFT_N-i);
					}
				} else {
					for (i=0; i<FFT_N; i++) { // save for next time
						nI++; nI %= nN;
						v_nexttime[i] += fft_notewave[nI] * (FFT_N-i);
					}
				}

				// TODO: make a 90-degree shifted version for another channel

				// align the note's iterator to the start of next fade-in
				nI -= FFT_N; nI %= nN;
				if (nI < 0) nI += nN;

				notes[note].i = nI;
			}

		}

		// end of processing in 'sections'
		// save some of the input samples for next time's FFT
		for (i=0; i<FFT_N/2; i++)
			fft_wave2[i] = in[i+nframes-FFT_N/2]*fft_window[i];
	}

	/***** FINAL PROCESSING *****/ FinalProcessing:;

	// apply input gain
	sample_t gain = pow(10,input_gain_dB/20.0);
	for (i=0; i<nframes; i++) out[i] *= gain;

	// apply compressor/limiter
	if (compressor_thresh < 0 // no use compressing if it'll distort anyway
	    && sizeof(sample_t)==4) // samples must be 32-bit float
	{
		static sample_t table[40] = {0};
		// set up a lookup table: the gain for each 3dB above threshold
		// faster than calling pow() for every sample
		if (table[0]==0) {
			table[0] = 1;
			table[1] = pow(2, 0.5/COMPRESSOR_RATIO-0.5);
			for (i=2; i<40; i++) table[i] = table[i-1]*table[1];
		}

		// calculate these values before the compressor loop
		// compressor_thresh rounds to a multiple of -3dB
		int bias = 127 + compressor_thresh/3;
		sample_t max = pow(2,40+(int)compressor_thresh/3);
		sample_t knee = pow(2,(int)compressor_thresh/3);
		sample_t coeff = (1.0-table[1])/0x00800000;

		// do the compressing
		static sample_t power = 0;
		for (i=0; i<nframes; i++)
		{
			power += (out[i]*out[i] - power) * (1.0f/COMPRESSOR_ATTACK);
			if (power >= max) out[i] *= table[39]*table[1];
			else if (power > knee)
			// break up float into exponent and mantissa, then interpolate
				out[i] *= table[((*(int*)&power & 0x7F800000)>>23)-bias]
				 * (1 - coeff * ((*(int*)&power & 0x007FFFFF)) );
		}

		// limit the peaks
		static sample_t peak=0;
		for (i=0; i<nframes; i++) {
			peak *= 1.0f-1.0f/LIMITER_RELEASE;
			if    ( -out[i] > peak) peak = -out[i];
			else if (out[i] > peak) peak =  out[i];
			if (peak > 1.0f) out[i] /= peak;
		}
	}
	else {
		// no compressor, just a hard limiter
		for (i=0; i<nframes; i++) {
			if      (out[i] < -1.0f) out[i] = -1.0f;
			else if (out[i] >  1.0f) out[i] =  1.0f;
		}
	}


	// record the voice to a file (with no echo/reverb)
	static short *wav16buf;
	static int started = 0;
	static int handle = -1;
	if (recording_to_file)
	{
		if (!started) {
			// open a wav file for recording
			char filename[80];
			time_t t; time(&t);
			strftime(filename,80,"SnoKoder_%F_%T.wav",localtime(&t));
			handle = creat(filename,0644);

			// create the wav file header
			write(handle,"RIFF",4);  // ChunkID
			write(handle,"????", 4); // ChunkSize
			write(handle,"WAVE",4);  // Format
			                     write(handle,"fmt ",4); // Subchunk1ID
			long value=16;       write(handle,&value,4); // Subchunk1Size
			value=1;             write(handle,&value,2); // AudioFormat
			value=1;             write(handle,&value,2); // NumChannels
			value=sample_rate;   write(handle,&value,4); // SampleRate
			value=sample_rate*2; write(handle,&value,4); // ByteRate
			value=2;             write(handle,&value,2); // BlockAlign
			value=16;            write(handle,&value,2); // BitsPerSample
			write(handle,"data",4); // Subchunk2ID
			write(handle,"????",4); // Subchunk2Size

			// allocate space for writing to the file
			wav16buf = malloc(nframes*2);

			// don't need to do all this again next time
			started = 1;
		}

		// convert the audio data to 16-bit and write it to the file
		for (i=0; i<nframes; i++) wav16buf[i] = out[i]*32767;
		write(handle, wav16buf, nframes*2);
	}
	else if (started) // if not recording anymore, finish up
	{
		// write the new ChunkSize (file size minus 8)
		long value = lseek(handle,0,SEEK_CUR)-8;
		lseek(handle,4,SEEK_SET);
		write(handle,&value,4);

		// write the new Subchunk2Size (file size minus 44)
		value -= 36;
		lseek(handle,40,SEEK_SET);
		write(handle,&value,4);

		// close the file and don't write to it again
		free(wav16buf);
		close(handle);
		started = 0;
	}


	// apply the echo/reverb
	if (using_echo)
	{
		static int read=0;
		static int write=0; if (clear_echo) write = read+echo_time;
		for (i=0; i<nframes; i++,read++,write++)
		{
			read &= ECHO_MAX-1;  // circular
			write &= ECHO_MAX-1; // buffer
			out[i] += echobuf[read];
			echobuf[read] = 0;
			echobuf[write] += out[i] * -0.125;
		}
	}


	// update flag-like variables
	if (clear_echo) clear_echo = 0;
	if (clear_noise) clear_noise = 0;
	lasttime_natural = thistime_natural;
	lasttime_vocoder = thistime_vocoder;

	return 0;
}



// function for dealing with any errors
void My_ErrorHandler (const char *desc)
{	fprintf (stderr, "JACK error: %s\n", desc);	}

// function for dealing with sample-rate changes
int My_SampleRateChange (jack_nframes_t nframes, void *arg)
{
	if (sample_rate > 0) {
		fprintf(stderr,"sample rate changed ... I QUIT!!!");
		return 1;
	}
	sample_rate = nframes;
	return 0;
}

// function for dealing with jack shutting down on you
void My_JackShutdown (void *arg)
{
	endwin();
	fprintf (stderr, "shut down!!!!! i dunno wtf happend????\n");
	exit (1);
}

// END OF JACK FUNCTIONS

void ClearNotes() // give the vocoder no notes
{
	int i; for (i=0; i<12; i++)
		notes[i].oct0 = notes[i].oct1 =
		notes[i].oct2 = notes[i].oct3 = 0;
}

void DrawDisplay() // set up the main user interface
{
	// initialize the display
	endwin(); initscr(); refresh();
	int width = getmaxx(stdscr);
	noecho(); cbreak(); clear();

	// if there was a window previously, delete it
	if (curses_window != NULL) delwin(curses_window);

	// start a new window
	curses_window = newwin(23,46, 0,(width-46)/2);

	// if the window could not be made
	if (curses_window == NULL) {
		curses_window = stdscr;
		mvaddstr(0,0,"TOO SMALL TO PROPERLY DISPLAY ANYTHING!");
		refresh();
		return;
	}

	// display the main user interface
	mvwprintw(curses_window, 0, 0,"\
  *   *   *  * * * * * * * * * *  *   *   *\n\r\
             * S.n.o.K.o.d.e.r *\n\r\
             * * * * * * * * * *\n\r\
\n\r\
HOW TO USE THIS PROGRAM:\n\r\
> sing or talk thru the microphone\n\r\
> press letters on keyboard to change notes\n\r\
  :\n\r\
       there are other keys too:\n\r\
  *keys*  |   *function*   |  *setting*\n\r\
----------|----------------|------------------\
 UP DOWN  | volume/gain    | %ddB\n\r\
LEFT RIGHT| formant shift  | %.2lf\n\r\
BACK\\SLASH| freqency bands | %s\n\r\
  ENTER   | note key mode  | %s\r\
BACKSPACE |-use-your-natural-voice-\n\r\
PGUP PGDN | musical scale  | %s maj / %s min\n\r\
   TAB    | voice through  | %s\r\
` TILDA ~ | noise removal  | %s\n\r\
SHFT+UP/DN| compressor     | %ddB threshold\n\r\
 SPACEBAR | tap out echoes | %s\n\r\
  INSERT  | record to file | %s\n\r\
----------^----------------^------------------",
		input_gain_dB,
		formant_shift,
		using_thin_bands? "thin (clearer)":"wide (fuzzier)",
		NOTES_MODE_NAMES[notes_mode],
		note_name[offset_key%12], note_name[(offset_key+9)%12],
		THRU_MODE_NAMES[thru_mode],
		noise_level>0 ? "ON":"OFF",
		compressor_thresh,
		using_echo? "echo":"no echoes",
		recording_to_file? "REC (no echo)":"STOPPED" );

	// draw a bit of a border around it
	if (width >= 48) {
		int i;
		for (i=1; i<21; i++) mvaddch(i, (width-46)/2 - 2, '-');
		refresh();
		for (i=1; i<21; i++) mvaddch(i, (width-46)/2 + 47, '-');
		refresh();
	}

	// move the cursor to where the notes are displayed
	wmove(curses_window, NOTES_Y, NOTES_X);
	wrefresh(curses_window);

	// call this function again if the terminal gets resized
	signal(SIGWINCH, DrawDisplay);
}

void NoteOn(int note) // add a note to the vocoder, 0 being the lowest note
{
	if(note < -128) return;
	if(note < 0)notes[(note%12+12)%12].oct0 = 1;
	else if (note < 12) notes[note%12].oct0 = 1;
	else if (note < 24) notes[note%12].oct1 = 1;
	else if (note < 36) notes[note%12].oct2 = 1;
	else                notes[note%12].oct3 = 1;
}

void NoteOff(int note)// erase a note from the vocoder, 0 being the lowest note
{
	if(note < -128) return;
	if(note < 0)notes[(note%12+12)%12].oct0 = 0;
	else if (note < 12) notes[note%12].oct0 = 0;
	else if (note < 24) notes[note%12].oct1 = 0;
	else if (note < 36) notes[note%12].oct2 = 0;
	else                notes[note%12].oct3 = 0;
}

void SetUpVocoder() // set up everything needed for the vocoder to work
{
	// FREQUENCY SYSTEMS

	// set up the FFT plans for the spectum analyzer
	plan_forward1 = fftw_plan_r2r_1d(FFT_N, fft_wave1, fft_freq1,
		FFTW_FORWARD, FFTW_ESTIMATE);
	plan_forward2 = fftw_plan_r2r_1d(FFT_N, fft_wave2, fft_freq2,
		FFTW_FORWARD, FFTW_ESTIMATE);
	plan_backward1 = fftw_plan_r2r_1d(FFT_N, fft_freq1, fft_wave1,
		FFTW_BACKWARD, FFTW_ESTIMATE);
	plan_backward2 = fftw_plan_r2r_1d(FFT_N, fft_freq2, fft_wave2,
		FFTW_BACKWARD, FFTW_ESTIMATE);

	// set up the spectrum analyzer FFT window (Hanning)
	int i; for (i=0; i<FFT_N; i++)
		fft_window[i] = 0.5 - 0.5*cos(M_PI*(2*i+1)/FFT_N);

	// set the filter response to flat for now
	for (i=0; i<FFT_N/2; i++) v_filt[i] = 1.00;

	// NOTE SYSTEMS

	// find the lowest note that still has less than FFT_N samples
	int offset = ceil (12 * log(sample_rate/110.0/FFT_N) / log(2));

	for (i=0; i<12; i++) // for each of the 12 notes:
	{
		// find its true note name
		note_name[i] = (char*)FIXED_NOTE_NAMES[(12+((i+offset)%12))%12];
		// set up the iFFT plan
		int N = sample_rate / 110.0 / pow(2, (i+offset)/12.0);
		notes[i].plan = fftw_plan_r2r_1d(N, fft_note, fft_notewave,
		                                 FFTW_BACKWARD, FFTW_ESTIMATE);
		notes[i].N = N;
		notes[i].i = 0;
		// initialize random phases
		N = N/2+N%2;
		notes[i].phases = malloc(N*sizeof(double));
		int j; for (j=0; j<N; j++) notes[i].phases[j]=M_PI*2*rand()/RAND_MAX;
	}
	// indicate which note is C (start of standard octave)
	offset_key = note_C = (12+((3-offset)%12))%12;
	// find the MIDI equivalent to the lowest possible vocoder note
	midi_LOW = 45 + offset;

	// FINAL PREPARATION

	// clear anything that's in the buffers
	ClearNotes();
	clear_echo = 1;
	clear_noise = 1;

	// vocoder is ready to roll!
	plans_are_made = 1;
}

void* WaitOnMIDI(void* ptr) // start a loop that responds to ALSA MIDI input
{
	int npfd;
	struct pollfd *pfd;
	npfd = snd_seq_poll_descriptors_count(seq_handle, POLLIN);
	pfd = (struct pollfd *)alloca(npfd * sizeof(struct pollfd));
	snd_seq_poll_descriptors(seq_handle, pfd, npfd, POLLIN);
	while (1)	if (poll(pfd, npfd, 100000) > 0) {
		snd_seq_event_t *ev;
		do {
			snd_seq_event_input(seq_handle, &ev);
			switch (ev->type) {
			case SND_SEQ_EVENT_NOTEON:
				// set the note in the vocoder
				if (ev->data.note.velocity > 0) // normal note-on
					NoteOn(ev->data.note.note - midi_LOW);
				else // velocity 0 - some keyboards use as note-off
					NoteOff(ev->data.note.note - midi_LOW);
			break;
			case SND_SEQ_EVENT_NOTEOFF: 
				// erase the note from the vocoder
				NoteOff(ev->data.note.note - midi_LOW);
			break;        
			}
			snd_seq_free_event(ev);
		} while (snd_seq_event_input_pending(seq_handle, 0) > 0);
	}
}

// main() handles the user interface and the startup/shutdown
int main (int argc, char *argv[])
{
	// first make sure SnoKoder is run in a terminal
	if (!getenv("TERM")) execlp("xterm","xterm","-hold","-e",argv[0],NULL);

	// display the basic program info
	printf("-- SnoKoder version 1.4 --\n\
Copyright (c) 2011, Elie Goldman Smith (pistough@hotmail.com)\n\
Released under the GNU General Public License V3 (FREE!YEAH!)\n.\n");

	// set up the everything to work with JACK
	if ((client = jack_client_new("SnoKoder")) == 0) {
		char name[32]; sprintf(name,"SnoKoder_%d",getpid());// try another name
		if ((client = jack_client_new(name)) == 0) {// or is jackd not running?
		 fprintf(stderr,"-- You must start JACK before running this program. --\n");
		 return 1;	}
	}
	jack_set_error_function (My_ErrorHandler);
	jack_set_process_callback (client, My_Process, 0);
	jack_set_sample_rate_callback (client, My_SampleRateChange, 0);
	jack_on_shutdown (client, My_JackShutdown, 0);
	input_port = jack_port_register (client, "input", 
	             JACK_DEFAULT_AUDIO_TYPE, JackPortIsInput, 0);
	output_port = jack_port_register (client, "output", 
	              JACK_DEFAULT_AUDIO_TYPE, JackPortIsOutput, 0);
	// force a good buffer size
	if (jack_get_buffer_size(client) < FFT_N)
		jack_set_buffer_size (client, FFT_N);
	// activate the client
	if (jack_activate (client))
	{	fprintf (stderr, "cannot activate client\n");
		return 1;	}
	// find some input ports to connect to
	const char **ports;
	ports=jack_get_ports(client,NULL,NULL,JackPortIsPhysical|JackPortIsOutput);
	if (ports == NULL) {
		fprintf(stderr, "cannot find any capture ports (microphone?)\n");
	} else {
		if (jack_connect (client, ports[0], jack_port_name (input_port)))
			fprintf (stderr, "cannot connect input ports\n");
		free(ports);
	}
	// find some output ports to connect to
	int i;
	ports=jack_get_ports(client,NULL,NULL,JackPortIsPhysical|JackPortIsInput);
	if (ports == NULL) {
		fprintf(stderr, "cannot find any playback ports (speakers?)\n");
	} else {
		for (i=0; ports[i]!=NULL; i++) {
		  if (jack_connect (client, jack_port_name(output_port), ports[i]))
		    fprintf (stderr, "cannot connect output ports\n");
		}
		free (ports);
	}

	// set up an ALSA midi port
	if (snd_seq_open(&seq_handle, "default", SND_SEQ_OPEN_INPUT, 0) < 0) {
		fprintf(stderr, "Error opening ALSA sequencer.\n");
		return 1;
	}
	snd_seq_set_client_name(seq_handle, "SnoKoder");
	if (snd_seq_create_simple_port(seq_handle, "SnoKoder",
		SND_SEQ_PORT_CAP_WRITE|SND_SEQ_PORT_CAP_SUBS_WRITE,
		SND_SEQ_PORT_TYPE_APPLICATION) < 0) {
		fprintf(stderr, "Error creating sequencer port.\n");
		return 1;
	}
	pthread_t MIDIthread; // automate midi handling
	pthread_create(&MIDIthread,NULL,WaitOnMIDI,NULL);

	/****************/
	SetUpVocoder();
	DrawDisplay();

	int upper_note = -500;
	int lower_note = -500;
	int the_note = -500;

	int quit=0;
	while (!quit)
	{
		clock_t lasttime;
		struct tms tcrap;
		int gotten;

		// get the next keypress
		gotten = toupper(getch());
		switch(gotten)
		{
		case 27: // the Escape keys
			mvwprintw(curses_window, NOTES_Y, NOTES_X,
				"PRESS <ESC> AGAIN TO QUIT"); wrefresh(curses_window);
			// get the next character in the escape sequence
			gotten = getch();
			if (gotten == 27) quit=1;
			else if (gotten == '[') {
				switch(getch()) {
				case 'A': // up arrow
					input_gain_dB++;
					mvwprintw(curses_window, INFO_Y+0, INFO_X,
						"%ddB\n", input_gain_dB);
				break;
				case 'B': // down arrow
					input_gain_dB--;
					mvwprintw(curses_window, INFO_Y+0, INFO_X,
						"%ddB\n", input_gain_dB);
				break;
				case 'C': // left arrow
					formant_shift += 0.05;
					if (formant_shift > 4.00) formant_shift = 4.00;
					mvwprintw(curses_window, INFO_Y+1, INFO_X,
						"%.2lf", formant_shift);
				break;
				case 'D': // right arrow
					formant_shift -= 0.05;
					if (formant_shift < 0.20) formant_shift = 0.20;
					mvwprintw(curses_window, INFO_Y+1, INFO_X,
						"%.2lf", formant_shift);
				break;
				case '1': // shift+arrowkeys
					if (getch()==';')
					if (getch()=='2')
					switch(getch()) {
					case 'A':
						compressor_thresh += 3;
						if (compressor_thresh < 0)
						  mvwprintw(curses_window, INFO_Y+8, INFO_X,
						    "%ddB threshold\n",compressor_thresh);
						else {
						  compressor_thresh = 0;
						  mvwprintw(curses_window,INFO_Y+8,INFO_X,"OFF\n");
						}
					break;
					case 'B':
						compressor_thresh -= 3;
						if (compressor_thresh < -60) compressor_thresh = -60;
						mvwprintw(curses_window, INFO_Y+8, INFO_X,
							"%ddB threshold\n",compressor_thresh);
					break;
					}
				break;
				case '2': // insert
				  if (recording_to_file) {
				      recording_to_file = 0;
				      mvwaddstr(curses_window,INFO_Y+10,INFO_X,"STOPPED\n");
				  } else {
				   recording_to_file = 1;
				   mvwaddstr(curses_window,INFO_Y+10,INFO_X,"REC (no echo)\n");
				  }
				getch();
				break;
				case '3': // delete
				getch();
				break;
				case '5': // page up
					if (offset_key<14) offset_key++;
					ClearNotes();
					mvwprintw(curses_window, INFO_Y+5, INFO_X,
						"%s maj / %s min\n",
						note_name[offset_key%12],
						note_name[(offset_key+9)%12] );
				getch();
				break;
				case '6': // page down
					if (offset_key>0) offset_key--;
					ClearNotes();
					mvwprintw(curses_window, INFO_Y+5, INFO_X,
						"%s maj / %s min\n",
						note_name[offset_key%12],
						note_name[(offset_key+9)%12] );
				getch();
				break;
				}
			}
			mvwaddch(curses_window, NOTES_Y, NOTES_X,'\n');
			gotten = 27;
		break;
		case ' ': // Spacebar: tap out echo timing
		{
			clock_t taps[4];
			int tap = 4;
			while ( tap > 0 && gotten == ' ' ) // ask for 4 spacebar presses
			{
				taps[--tap] = times(&tcrap);
				mvwprintw(curses_window,INFO_Y+9,INFO_X,"%d more...\n",tap);
				wrefresh(curses_window);
				if (tap>0) gotten = getch();
			}
			if (gotten == ' ') // if spacebar was tapped 4 times:
			{
				// check that the spacebar was tapped rhythmically enough
				if(abs( (taps[0]-taps[1])/1.0 - (taps[0]-taps[3])/3.0 ) < 10
				&& abs( (taps[0]-taps[2])/2.0 - (taps[0]-taps[3])/3.0 ) < 10)
				{
					// set echoes to new rhythm
					echo_time = sample_rate * (taps[0]-taps[3])/3.0 / 100.0;
					if (echo_time < ECHO_MAX) using_echo = 1;
					else using_echo = 0; // if too long, turn off echoes
				}
				else using_echo = 0; // if not rhythmic, turn off echoes

				clear_echo = 1; // clear the previous echoes
			}
			else ungetch(gotten); // forget it, deal with some other keypress

			// re-display the info about the echoes
			if (using_echo) mvwprintw(curses_window,INFO_Y+9,INFO_X,
			                "%ld msec\n",1000*echo_time/sample_rate );
			else mvwprintw(curses_window,INFO_Y+9,INFO_X,"no echoes\n");
		}
		break;
		case '\n': // Enter: switch note keying mode
			switch (notes_mode) {
			case NOTES_SINGLE: notes_mode = NOTES_DOUBLE; break;
			case NOTES_DOUBLE: notes_mode = NOTES_CHORDS; break;
			case NOTES_CHORDS: notes_mode = NOTES_SINGLE; break;
			}
			mvwaddstr(curses_window, INFO_Y+3, INFO_X,
			          NOTES_MODE_NAMES[notes_mode] );
		break;
		case '\t': // Tab: switch voice-through mode
			switch (thru_mode) {
			case THRU_NONE: thru_mode = THRU_REALFAKE; break;
			case THRU_REALFAKE: thru_mode = THRU_NONE; break;
			}
			mvwaddstr(curses_window, INFO_Y+6, INFO_X,
			          THRU_MODE_NAMES[thru_mode] );
		break;
		case 8: case 127: // Backspace: clear notes, use your real voice
			ClearNotes();
			the_note = lower_note = upper_note = -500;
		break;
		case 'Z': the_note = lower_note = 0; break;
		case 'S': the_note = lower_note = 1; break;
		case 'X': the_note = lower_note = 2; break;
		case 'D': the_note = lower_note = 3; break;
		case 'C': the_note = lower_note = 4; break;
		case 'V': the_note = lower_note = 5; break;
		case 'G': the_note = lower_note = 6; break;
		case 'B': the_note = lower_note = 7; break;
		case 'H': the_note = lower_note = 8; break;
		case 'N': the_note = lower_note = 9; break;
		case 'J': the_note = lower_note = 10; break;
		case 'M': the_note = lower_note = 11; break;
		case ',': the_note = lower_note = 12; break;
		case 'L': the_note = lower_note = 13; break;
		case '.': the_note = lower_note = 14; break;
		case ';': the_note = lower_note = 15; break;
		case '/': the_note = lower_note = 16; break;
		case 'Q': the_note = upper_note = 12; break;
		case '2': the_note = upper_note = 13; break;
		case 'W': the_note = upper_note = 14; break;
		case '3': the_note = upper_note = 15; break;
		case 'E': the_note = upper_note = 16; break;
		case 'R': the_note = upper_note = 17; break;
		case '5': the_note = upper_note = 18; break;
		case 'T': the_note = upper_note = 19; break;
		case '6': the_note = upper_note = 20; break;
		case 'Y': the_note = upper_note = 21; break;
		case '7': the_note = upper_note = 22; break;
		case 'U': the_note = upper_note = 23; break;
		case 'I': the_note = upper_note = 24; break;
		case '9': the_note = upper_note = 25; break;
		case 'O': the_note = upper_note = 26; break;
		case '0': the_note = upper_note = 27; break;
		case 'P': the_note = upper_note = 28; break;
		case '[': the_note = upper_note = 29; break;
		case '=': the_note = upper_note = 30; break;
		case ']': the_note = upper_note = 31; break;
		case '`': case '~':
			if (noise_level > 0) { // if theres already noise collected
				clear_noise = 1;
				mvwprintw(curses_window, INFO_Y+7, INFO_X, "OFF\n");
			}
			else {
				clear_noise = 1;
				mvwprintw(curses_window,INFO_Y+7,INFO_X,"QUIET ONE SECOND!");
				wrefresh(curses_window);
				collecting_noise = 1; // My_Process() will
				sleep(1);             // collect the noise
				collecting_noise = 0; // for one second
				mvwprintw(curses_window, INFO_Y+7, INFO_X, "ON\n");
			}
		break;
		case '\\': case '|':
			if (using_thin_bands) {
				using_thin_bands=0;
				mvwaddstr(curses_window,INFO_Y+2,INFO_X,"wide (fuzzier)\n");
			}
			else {
				using_thin_bands=1;
				mvwaddstr(curses_window,INFO_Y+2,INFO_X,"thin (clearer)\n");
			}
		break;
		}

		// set up which notes are to be vocoded
		switch(notes_mode) {
		case NOTES_SINGLE:
			ClearNotes();
			// just put the one note into the vocoder
			NoteOn(the_note + offset_key);
		break;
		case NOTES_DOUBLE:
			ClearNotes();
			// let there always be two notes into the vocoder
			NoteOn(upper_note + offset_key);
			NoteOn(lower_note + offset_key);
		break;
		case NOTES_CHORDS:
			// if it was a note key that was pressed:
			if (the_note >= 0)
			{
				// start a new chord if keypresses were more than 1/25sec apart
				if ( times(&tcrap)-lasttime > 100/25 ) ClearNotes();
				// do a timestamp for next time
				lasttime = times(&tcrap);
				// put the keypressed note into the vocoder
				NoteOn(the_note + offset_key);
				// don't do this again until another note key is pressed
				the_note = -500;
			}
		break;
		}

		// show which notes are being vocoded
		mvwaddch(curses_window, NOTES_Y, NOTES_X,'\n');
		wmove(curses_window, NOTES_Y, NOTES_X);
		for(i=0;i<12;i++) if(notes[i].oct0>0)
			wprintw(curses_window, "%s%c ", note_name[i], i<note_C ? '0':'1');
		for(i=0;i<12;i++) if(notes[i].oct1>0)
			wprintw(curses_window, "%s%c ", note_name[i], i<note_C ? '1':'2');
		for(i=0;i<12;i++) if(notes[i].oct2>0)
			wprintw(curses_window, "%s%c ", note_name[i], i<note_C ? '2':'3');
		for(i=0;i<12;i++) if(notes[i].oct3>0)
			wprintw(curses_window, "%s%c ", note_name[i], i<note_C ? '3':'4');

		// update the text display
		wrefresh(curses_window);
	}

 // END OF PROGRAM:
	endwin();

	if (recording_to_file) {
		recording_to_file = 0;
		sleep(1);
	}
	jack_client_close (client);

	fftw_destroy_plan(plan_forward1);
	fftw_destroy_plan(plan_forward2);
	for (i=0; i<12; i++) {
		fftw_destroy_plan(notes[i].plan);
		free(notes[i].phases);
	}

	return 0;
}

