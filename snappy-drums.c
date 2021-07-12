/***
 Elie's snappy drum machine!
 Designed to be as versitile as 808s, but ready to cut through any mix.
 Version: 1.1
 --

 To compile this:
    gcc snappy-drums.c -lpthread -lm -ljack -lcurses -lasound -O3 -ffast-math -o snappy-drums


 Copyright 2019, Elie Goldman Smith

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

#include <alsa/asoundlib.h>
#include <ctype.h>
#include <curses.h>
#include <jack/jack.h>
#include <math.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/times.h>
#include <time.h>
#include <unistd.h>

// macros etc to make code look cleaner
typedef jack_default_audio_sample_t sample_t;
#define STATE(b)   ((b)?"ON":"OFF")
#define MIDI_TO_FREQ(m)  (440*pow(2, 0.08333333333333333*((m)-69)))
#define isSubnormalF(f)  ((*(unsigned*)&(f) & 0x7F800000) == 0)

// constants
#define CLIENT_NAME "snappy"
#define LOW_FREQUENCY_ROLLOFF 46 // hz    
#define LOW_FREQUENCY_CUTOFF 39 // hz        or try 48.8hz and 41.4hz
// default controller values
// note: most globals don't reset to these, but rather to a number based on these.
#define DCV_CLAP 0.00025 // or try 0.0004 but comment out //ca *= g_clapDecayFactor;
#define DCV_HH 0.001
#define DCV_DECAY 0.04
#define DCV_SWEEP_SPEED 7
#define DCV_AUX_DECAY 0.02
#define DCV_AUX_RELEASE 0.14
#define DCV_CYMBAL 0.001
#define DCV_COWBELL 0.004

// Important Globals

snd_seq_t* g_seqHandle; // ALSA midi handle
jack_client_t* g_client;   // JACK
jack_port_t* g_outputPort; // globals

long g_sampleRate = -1;
char g_keys[128]; // keyboard character -> midi note
int g_qw[128]; // midi note -> quarter wavelength
int g_quarterWaveFade = 275; // used for removing frequencies that are too low
int g_quarterWaveMax = 300;  //
int g_initialized = 0; // flag to tell My_Process and WaitOnMIDI that we're ready
sample_t g_masterVolume = 1.0;

// tone drums
volatile int g_newToneDrum = 0;
volatile int g_tdQuarterWave = 100;
volatile int g_tdSweepSpeed = DCV_SWEEP_SPEED;
volatile sample_t g_tdDecayFactor = -1.0+DCV_DECAY;
volatile sample_t g_tdNoisiness = 0;
volatile sample_t g_tdVolume = 0.5;

// claps
volatile int g_newClap = 0; // boolean
volatile sample_t g_clapDecayFactor = 1.0-DCV_CLAP;
volatile sample_t g_clapVolume = 0.2;

// high hats
volatile int g_newHighHat = 0; // boolean
volatile sample_t g_hhDecayFactor = 1.0-DCV_HH;
volatile sample_t g_hhVolume = 0.2;

// auxillary tones
volatile int g_newAuxTone = 0; // boolean
volatile int g_atQuarterWave = 50;
volatile sample_t g_atDecayFactor = -1.0+DCV_AUX_DECAY;
volatile sample_t g_atVolume = 0.2;

// cowbells
volatile int g_newCowbell = 0; // boolean
volatile int g_cbWaveScale = 4;
volatile sample_t g_cbDecayFactor = 1.0-DCV_COWBELL;
volatile sample_t g_cbVolume = 0.5;

// cymbals
#define CYMBAL_N 6 // number of tones (square waves)
volatile int g_newCymbal = 0; // boolean
volatile int g_cymTones[CYMBAL_N] = {3, 4, 7, 11, 18, 29}; // half wavelengths
volatile sample_t g_cymDecayFactor = 1.0-DCV_CYMBAL;
volatile sample_t g_cymVolume = 0.2;



// all AUDIO INPUT AND OUTPUT code in this next function:
int My_Process (jack_nframes_t nframes, void *arg)
{
 // get the pointers to the in[] and out[] audio buffers
 sample_t *out = (sample_t *) jack_port_get_buffer(g_outputPort, nframes);
 int i;

 // make sure we're ready
 if (!g_initialized) {
  if (out != NULL) memset(out, 0, nframes*sizeof(sample_t));
  return 0;
 }

 // make sure parameters are valid
 if (g_hhDecayFactor < 0) g_hhDecayFactor = -g_hhDecayFactor;
 if (g_hhDecayFactor > 1) g_hhDecayFactor = 1;
 if (g_clapDecayFactor < 0) g_clapDecayFactor = -g_clapDecayFactor;
 if (g_clapDecayFactor > 1) g_clapDecayFactor = 1;
 if (g_tdDecayFactor > 0) g_tdDecayFactor = -g_tdDecayFactor;
 if (g_tdDecayFactor < -1) g_tdDecayFactor = -1;
 if (g_tdQuarterWave < 1) g_tdQuarterWave = 1;
 if (g_tdNoisiness > g_tdQuarterWave-1) g_tdNoisiness = g_tdQuarterWave-1;
 if (g_tdSweepSpeed < 1) g_tdSweepSpeed = 1;
 if (g_atQuarterWave < 1) g_atQuarterWave = 1;
 if (g_atDecayFactor > 0) g_atDecayFactor = -g_atDecayFactor;
 if (g_atDecayFactor < -1) g_atDecayFactor = -1;
 if (g_cbDecayFactor < -1) g_cbDecayFactor = -1;
 if (g_cbDecayFactor > 1) g_cbDecayFactor = 1;
 if (g_cbWaveScale < 1) g_cbWaveScale = 1;
 if (g_cymDecayFactor < 0) g_cymDecayFactor = -g_cymDecayFactor;
 if (g_cymDecayFactor > 1) g_cymDecayFactor = 1;


 // Tone Drums
 static sample_t s = 0; // audio signal
 static sample_t ds = 0;// rate of change
 static int n = 1; // current number of samples in a line
 static int count = 1; // sample counter within a line
 static int lines = 6; // line counter (resets every few lines)
 static int plateau = 1; // boolean state: is line a plateau or a slope
 static int attack = 1; // boolean state: are we in the attack stage or the tone stage
 static sample_t a = 0; // current peak amplitude of wave; oscillates between + and -
 static sample_t fm = 0; // frequency modulation for noisiness
 static sample_t dfm = 0;// rate of change
 static sample_t lfRolloffSlope = 0.04;// used for removing frequencies that are too low
 static sample_t attf = 0; // for calcuating decays during sweep

 if (g_newToneDrum) {
  g_newToneDrum = -1;
  if      (s > 0) s = a = -g_tdVolume;   // polarity
  else if (s < 0) s = a =  g_tdVolume;   //
  else            s = a =  (rand()&1) ? -g_tdVolume : g_tdVolume;
  ds = 0;
  plateau = 1;
  attack = 1;
  lines = 6;
  fm = dfm = 0;
  lfRolloffSlope = 1.0 / (g_quarterWaveMax - g_quarterWaveFade);

  count = n = g_tdSweepSpeed*2;
  if (g_tdQuarterWave > g_quarterWaveMax) g_tdQuarterWave = g_quarterWaveMax;
  attf = (g_tdDecayFactor + 1.0) / g_tdQuarterWave;

  if (n < g_tdQuarterWave) {
   // this is to correct for amplitude decay during sweep
   a *= pow(-g_tdDecayFactor, 0.25 - 0.25 * g_tdQuarterWave / g_tdSweepSpeed);
   s = a;
  }
  else count = n = g_tdQuarterWave;
 }

 // output loop
 if (a != 0 || s != 0 || ds != 0) {
  for (i=0; i<nframes; i++) {
   s += ds;
   out[i] = s;
   
   /* uncomment this to add some nasty grit:
   if      (s > fabs(a)*0.001) out[i] += fabs(a)*0.25;
   else if (s < fabs(a)*0.001) out[i] -= fabs(a)*0.25; */

   if (--count <= 0) {
    if (attack) {
     n += g_tdSweepSpeed;
     if (n >= g_tdQuarterWave) attack = 0;
    }
    if (!attack) {
     n = g_tdQuarterWave;
     if (g_tdNoisiness) {
      fm += dfm;
      n += fm + 0.5;
      if (n < 1) n = 1;
      if (--lines <= 0) {
       lines = 6;
       dfm = (1.0/6.0) * (g_tdNoisiness*(rand()*(2.0/RAND_MAX)-1.0) - fm);
      }
     }
    }
    if (plateau) {
     plateau = 0;

     if (attack) a *= -1.0 + n*attf;
     else a *= g_tdDecayFactor;

     if    (n <= g_quarterWaveFade) ds = (a - s) / n;
     else if (n < g_quarterWaveMax) ds = (a*(g_quarterWaveMax-n)*lfRolloffSlope - s) / n;
     else ds = -s / n;

     if (isSubnormalF(a)) a = 0;
     if (isSubnormalF(s)) s = 0;
     if (isSubnormalF(ds)) ds = 0;
    }
    else {
     plateau = 1;
     ds = 0;
     if (isSubnormalF(s)) s = 0;
    }
    count = n;
   }
  }
 }
 else memset(out, 0, nframes*sizeof(sample_t));


 // Claps and High Hats
 static sample_t n0 = 0; // white noise buffer: 3 samples for simple convolutions
 static sample_t n1 = 0; //
 static sample_t n2 = 0; //
 static sample_t f1s = 0; // filter stage for clap noise
 static sample_t f2s = 0; // another filter stage for clap noise
 static sample_t f2c = 1; // filter coefficient for clap noise
 static int clapTicks = 0; // clap starts with some decaying 'ticks', each 512 samples
 static int clapTime = 512; // sample position within a clap tick
 static sample_t ca = 0; // clap amplitude
 static sample_t ha = 0; // high hat amplitude

 if (g_newClap) {
  g_newClap = 0;
  ca = g_clapVolume;
  f2c = 1;
  if (g_newToneDrum == -1) clapTicks = 0;
  else                     clapTicks = 2;
  clapTime = 512;
 }
 if (g_newHighHat) {
  g_newHighHat = 0;
  ha = g_hhVolume;
 }

 // output loop
 if (ca != 0 || ha != 0) {
  for (i=0; i<nframes; i++) {
   n2 = n1;
   n1 = n0;
   n0 = rand() * (2.0/RAND_MAX) - 1.0;

   // clap
   sample_t clapNoise = n0 + 2*n1 + n2 - f1s;
   f1s += clapNoise * 0.008;
   f2s += (clapNoise - f2s) * f2c;

   if (clapTicks <= 0) {
    out[i] += ca * f2s;
    ca *= g_clapDecayFactor;
   }
   else {
    out[i] += ca * f2s * (2.0/512.0/512.0/512.0)*clapTime*clapTime*clapTime;
    if (--clapTime <= 0) {
     clapTime = 512;
     clapTicks--;
    }
   }
   f2c *= g_clapDecayFactor;

   // high hats
   out[i] -= ha * (n0 - 2*n1 + n2);
   ha *= g_hhDecayFactor;

   // avoid subnormal numbers, because they could waste CPU cycles
   if (isSubnormalF(ca)) ca = 0;
   if (isSubnormalF(ha)) ha = 0;
   if (isSubnormalF(f2c)) f2c = 0;
  }
 }

 // Auxillary Tones
 static sample_t as = 0;
 static sample_t ads = 0;
 static sample_t aa = 0;
 static int acount = 0;
 static int aplateau = 0;
 if (g_newAuxTone) {
  g_newAuxTone = 0;
  if      (as > 0) aa =  g_atVolume;   // polarity
  else if (as < 0) aa = -g_atVolume;   //
  else             aa =  (rand()&1) ? -g_atVolume : g_atVolume;
  acount = 0;
  aplateau = 1;
 }
 if (aa != 0 || as != 0 || ads != 0) {
  for (i=0; i<nframes; i++) {
   as += ads;
   out[i] += as;

   if (--acount <= 0) {
    acount = g_atQuarterWave;
    if (aplateau) {
     aplateau = 0;
     aa *= g_atDecayFactor;
     if (g_atQuarterWave < g_quarterWaveMax) ads = (aa - as) / acount;
     else ads = -as / acount;
     if (isSubnormalF(aa)) aa = 0;
     if (isSubnormalF(as)) as = 0;
     if (isSubnormalF(ads)) ads = 0;
    }
    else {
     aplateau = 1;
     ads = 0;
     if (isSubnormalF(as)) as = 0;
    }
   }
  }
 }
 
 // Cowbell
 {
  // A mix of two slanted triangle-waves, with a frequency ratio of 2/3
  // This is implemented as a line graph.
  static const int N = 9;
  static const int lengths[] = {2,1,5,2,2,3,1,2,6};
  static const int slopes[] = {15, 3, -5, 7, -5, 3, -5, 7, -5};
  static const int DC = 18;
  static int s = -DC;
  static int p = 0;
  static int count = 2;
  static sample_t a = 0;
  if (g_newCowbell) {
   g_newCowbell = 0;
   p = 0;
   count = lengths[0] * g_cbWaveScale;
   s = -DC * g_cbWaveScale;
   a = 0.04 * g_cbVolume / g_cbWaveScale; if (rand()&1) a = -a;
  }
  // output loop
  if (a != 0 && g_cbWaveScale > 0 && g_cbWaveScale*3 <= g_quarterWaveFade) {
   for (i=0; i<nframes; i++) {
    out[i] += s*a;
    s += slopes[p];
    if (--count <= 0) {
     if (++p >= N) p = 0;
     count = lengths[p] * g_cbWaveScale;
    }
    a *= g_cbDecayFactor;
    if (isSubnormalF(a)) a=0;
   }
  }
 }

 // Cymbal
 {
  static int phases[CYMBAL_N];
  static sample_t a = 0; // amplitude
  static sample_t f = 1; // lowpass filter coefficient
  static sample_t s = 0; // lowpass filter state
  static sample_t s2 = 0; // highpass filter state
  if (g_newCymbal) {
   g_newCymbal = 0;
   a = s = s2 = 0;
   f = 1;
   for (i=0; i<CYMBAL_N; i++) {
    //phases[i] = 0;
    a += g_cymTones[i];
   }
   if (rand()&1) a = -a;
   if (a != 0) a = 0.4*g_cymVolume / a; // 'a' should never be zero here tho
  }
  if (a != 0 && f != 0) { // here, 'a' can be zero if the cymbal is done ringing.
   for (i=0; i<nframes; i++) {
    int v=0, j=0;
    for (; j<CYMBAL_N; j++) {
     if (phases[j] < 0) v += g_cymTones[j]; else v -= g_cymTones[j];
     if (++phases[j] >= g_cymTones[j]) phases[j] = -g_cymTones[j];
    }
    s += (v*a-s)*f;
    s2 += (s-s2)*0.1;
    out[i] += s - s2;

    //a *= g_cymDecayFactor;
    f *= g_cymDecayFactor;
    if (isSubnormalF(a)) a = 0;
    if (isSubnormalF(f)) f = 0;
   }
  }
 }
 
 if (g_newToneDrum == -1) g_newToneDrum = 0;
 return 0;
}




// function for dealing with any errors
void My_ErrorHandler (const char *desc)
 { fprintf (stderr, "JACK error: %s\n", desc); }

// function for dealing with sample-rate changes
int My_SampleRateChange (jack_nframes_t nframes, void *arg)
{
 if (g_sampleRate > 0) {
  // Maybe it's safe to handle a sample rate change just by
  // calling SetUpNotes() again, but I'm not sure.
  // For now, just leave it.
  fprintf(stderr,"sample rate changed ... I QUIT!!!");
  return 1;
 }
 g_sampleRate = nframes;
 return 0;
}

// function for dealing with jack shutting down on you
void My_JackShutdown (void *arg)
{
 fprintf (stderr, "shut down!!!!! i dunno wtf happend????\n");
 exit (1);
}

// END OF JACK FUNCTIONS


// function that starts a loop that responds to ALSA MIDI input
void* WaitOnMIDI(void* ptr)
{
 int tdQW = 100;
 int atQW = 100;
 // values affected by controllers:
 sample_t tdBend = 1;
 sample_t atBend = 1;
 sample_t clapTweak = DCV_CLAP;
 sample_t hhTweak = DCV_HH;
 sample_t atDecay = -1.0+DCV_AUX_DECAY;
 sample_t atRelease = -1.0+DCV_AUX_RELEASE;
 sample_t cbTweak = DCV_COWBELL;
 sample_t cymTweak = DCV_CYMBAL;

 while (!g_initialized) sleep(1);

 int npfd;
 struct pollfd *pfd;
 npfd = snd_seq_poll_descriptors_count(g_seqHandle, POLLIN);
 pfd = (struct pollfd *)alloca(npfd * sizeof(struct pollfd));
 snd_seq_poll_descriptors(g_seqHandle, pfd, npfd, POLLIN);
 while (1) if (poll(pfd, npfd, 100000) > 0) {
  snd_seq_event_t *ev;
  do {
   snd_seq_event_input(g_seqHandle, &ev);
   switch (ev->type) {
   case SND_SEQ_EVENT_NOTEON:
   {
    // XXX: should i put a mutex to make sure jack process isnt running?
    // XXX: can i somehow tell the kernel "dont interrupt the thread until all these lines of code are executed"?
    int qw = g_qw[ev->data.note.note];
    sample_t v = (1.0/127.0) * ev->data.note.velocity; v *= v * g_masterVolume;
    if (v > 0) {
     if (ev->data.control.channel != 15) {
      if (qw > 0) {                    // Tone Drums
       tdQW = qw;
       qw = 0.5+qw*tdBend;
       if (!g_newToneDrum) {
        g_newToneDrum = 1;
        g_tdQuarterWave = qw;
        g_tdVolume = v;
        g_tdNoisiness = 0;
       }
       else { // if another tone drum was already received, do a ghost drum
        g_tdNoisiness = (qw - g_tdQuarterWave)*0.5;
        g_tdQuarterWave = (qw + g_tdQuarterWave)*0.5;
        g_tdVolume = (v+g_tdVolume)*0.5;
       }
      }
      else if (qw == 0 || qw == -1) { // Claps
       sample_t cdf;
       if (qw == 0) cdf = 1.0-clapTweak;
       else         cdf = 1.0-clapTweak*0.5;
       v *= 0.3;
       if (!g_newClap) {
        g_newClap = 1;
        g_clapVolume = v;
        g_clapDecayFactor = cdf;
       }
       else { // if another clap was already received, pick the loudest and longest
        if (g_clapVolume < v) g_clapVolume = v;
        if (g_clapDecayFactor < cdf) g_clapDecayFactor = cdf;
       }
      }
      else if (qw == -2 || qw == -3) { // High Hats
       sample_t hdf;
       if (qw == -3) hdf = 1.0-hhTweak;
       else          hdf = 1.0-hhTweak*0.25;
       v *= 0.2;
       if (!g_newHighHat) {
        g_newHighHat = 1;
        g_hhVolume = v;
        g_hhDecayFactor = hdf;
       }
       else { // if another hihat was already received, pick the loudest and longest
        if (g_hhVolume < v) g_hhVolume = v;
        if (g_hhDecayFactor < hdf) g_hhDecayFactor = hdf;
       }
      }
     } 
     else {
      if (qw > 0) {                     // Aux Tones
       atQW = qw;
       qw = 0.5+qw*atBend;
       g_newAuxTone = 1;
       g_atQuarterWave = qw;
       g_atVolume = v*0.4;
       g_atDecayFactor = atDecay;
      }
      else switch(ev->data.note.note) { // Cymbals
       case 127:
        g_newCymbal = 1;
        g_cymVolume = v*0.5;
        g_cymDecayFactor = 1.0-cymTweak;
        g_cymTones[0] = 9;
        g_cymTones[1] = 17;
        g_cymTones[2] = 26;
        g_cymTones[3] = 43;
        g_cymTones[4] = 69;
        g_cymTones[5] = 112; // fibonacci 1
       break;
       case 126:
        g_newCymbal = 1;
        g_cymVolume = v;
        g_cymDecayFactor = 1.0-cymTweak*0.1;
        g_cymTones[1] = 17;
        g_cymTones[2] = 26;
        g_cymTones[3] = 43;
        g_cymTones[4] = 69;
        g_cymTones[5] = 112;
        g_cymTones[0] = 181; // same as above, but deeper
       break;
       case 125:
        g_newCymbal = 1;
        g_cymVolume = v*0.5;
        g_cymDecayFactor = 1.0-cymTweak;
        g_cymTones[0] = 11;
        g_cymTones[1] = 19;
        g_cymTones[2] = 30;
        g_cymTones[3] = 49;
        g_cymTones[4] = 79;
        g_cymTones[5] = 128; // fibonacci 2
       break;
       case 124:
        g_newCymbal = 1;
        g_cymVolume = v;
        g_cymDecayFactor = 1.0-cymTweak*0.1;
        g_cymTones[1] = 19;
        g_cymTones[2] = 30;
        g_cymTones[3] = 49;
        g_cymTones[4] = 79;
        g_cymTones[5] = 128;
        g_cymTones[0] = 207; // same as above, but deeper
       break;
       case 123:
        g_newCymbal = 1;
        g_cymVolume = v*0.5;
        g_cymDecayFactor = 1.0-cymTweak;
        g_cymTones[0] = 13;
        g_cymTones[1] = 21;
        g_cymTones[2] = 34;
        g_cymTones[3] = 55;
        g_cymTones[4] = 89;
        g_cymTones[5] = 144; // fibonacci 3
       break;
       case 122:
        g_newCymbal = 1;
        g_cymVolume = v;
        g_cymDecayFactor = 1.0-cymTweak*0.1;
        g_cymTones[1] = 21;
        g_cymTones[2] = 34;
        g_cymTones[3] = 55;
        g_cymTones[4] = 89;
        g_cymTones[5] = 144;
        g_cymTones[0] = 233; // same as above, but deeper
       break;
       case 121:
        g_newCymbal = 1;
        g_cymVolume = v*0.5;
        g_cymDecayFactor = 1.0-cymTweak;
        g_cymTones[0] = 48;
        g_cymTones[1] = 59;
        g_cymTones[2] = 71;
        g_cymTones[3] = 85;
        g_cymTones[4] = 101;
        g_cymTones[5] = 121; // coprime evenly spaced spectrum 1
       break;
       case 120:
        g_newCymbal = 1;
        g_cymVolume = v;
        g_cymDecayFactor = 1.0-cymTweak*0.1;
        g_cymTones[3] = 85;
        g_cymTones[4] = 101;
        g_cymTones[5] = 121;
        g_cymTones[0] = 148; // same as above, but deeper
        g_cymTones[1] = 177;
        g_cymTones[2] = 211;
       break;
       default:                         // Cowbells
        g_cbVolume = v;
        g_cbWaveScale = 120 - ev->data.note.note;
        g_cbDecayFactor = 1.0-cbTweak/g_cbWaveScale;
        g_newCowbell = 1;
      }
     }
    }
   }
   break;
   case SND_SEQ_EVENT_NOTEOFF:
    if (ev->data.control.channel == 15 &&
     g_qw[ev->data.note.note] == atQW)
      g_atDecayFactor = atRelease;
   break;
   case SND_SEQ_EVENT_PITCHBEND:
   {
    sample_t bend = exp(ev->data.control.value*(-M_LN2/8192.0));
    if (ev->data.control.channel == 15) {
     g_atQuarterWave = 0.5+atQW*bend;
     atBend = bend;
    }
    else {
     g_tdQuarterWave = 0.5+tdQW*bend;
     tdBend = bend;
    }
   }
   break;
   case SND_SEQ_EVENT_CONTROLLER:
    if (ev->data.control.param == 7) {       // Master Volume (all channels)
     g_masterVolume = (1.0/127.0/127.0)*ev->data.control.value*ev->data.control.value;
    }
    else if (ev->data.control.param == 70 && ev->data.control.channel != 15) {
                                             // Sound Variation
     g_tdSweepSpeed = (127-ev->data.control.value)*((DCV_SWEEP_SPEED-1)/63.0)+1.5;
    }
    else if (ev->data.control.param == 71) { // Sound Timbre
     if (ev->data.control.channel == 15) atDecay = -1.0 + (127-ev->data.control.value)*(DCV_AUX_DECAY/63.0);
    }
    else if (ev->data.control.param == 72) { // Sound Release Time
     if (ev->data.control.channel == 15) atRelease = -1.0 + DCV_AUX_RELEASE*1.5 - ev->data.control.value * (DCV_AUX_RELEASE*0.5 / 64.0);
     else g_tdDecayFactor = -1.0 + (127-ev->data.control.value) * (DCV_DECAY/63.0);
    }
    else if (ev->data.control.param == 75) { // Sound Control 6 (clap)
     if (ev->data.control.channel == 15)
      cbTweak = DCV_COWBELL*1.5-ev->data.control.value*(DCV_COWBELL*0.5/64.0);
     else clapTweak = DCV_CLAP*1.5-ev->data.control.value*(DCV_CLAP*0.5/64.0);
    }
    else if (ev->data.control.param == 76) { // Sound Control 7 (high hats)
     if (ev->data.control.channel == 15)
      cymTweak = DCV_CYMBAL*1.5-ev->data.control.value*(DCV_CYMBAL*0.5/64.0);
     else hhTweak = DCV_HH*1.5 - ev->data.control.value * (DCV_HH*0.5 / 64.0);
    }
    else if (ev->data.control.param == 121) { // All Controllers Off (all channels)
     g_masterVolume = 1.0;
     g_tdSweepSpeed = DCV_SWEEP_SPEED;
     g_tdDecayFactor = -1.0 + DCV_DECAY;
     tdBend = 1;
     atBend = 1;
     clapTweak = DCV_CLAP;
     hhTweak = DCV_HH;
     atDecay = -1.0+DCV_AUX_DECAY;
     atRelease = -1.0+DCV_AUX_RELEASE;
     cbTweak = DCV_COWBELL;
     cymTweak = DCV_CYMBAL;
    }
    else if (ev->data.control.param == 120) { // All Sound Off (all channels)
     g_tdVolume = g_clapVolume = g_hhVolume = g_atVolume = g_cbVolume = g_cymVolume = 0;
     g_newToneDrum = g_newClap = g_newHighHat = g_newAuxTone = g_newCowbell = g_newCymbal = 1;
    }
    if (ev->data.control.param == 123) {      // All Notes Off (all channels)
     g_tdQuarterWave = g_quarterWaveMax+1;
     g_clapDecayFactor = 0.999;           
     g_hhDecayFactor = 0.998;
     g_atDecayFactor = -0.8;
     g_cbDecayFactor = 0.996;
     g_cymDecayFactor = 0.998;
    }
   break;
   }
   snd_seq_free_event(ev);
  } while (snd_seq_event_input_pending(g_seqHandle, 0) > 0);
 }
}

int SetUpNotes() {
 if (g_sampleRate < 1) return -1;
 int i; for (i=0; i<128; i++) g_keys[i] = -1;
 char *row1l = "zsxdcvgbhnjm,l.;/";
 char *row1u = "ZSXDCVGBHNJM<L>:?";
 char *row2l = "q2w3er5t6y7ui9o0p[=]\n";
 char *row2u = "Q@W#ER%T^Y&UI(O)P{+}";
 for (i=0; row1l[i] != '\0'; i++) g_keys[row1l[i]] = i+24;
 for (i=0; row2l[i] != '\0'; i++) g_keys[row2l[i]] = i+36;
 for (i=0; row1u[i] != '\0'; i++) g_keys[row1u[i]] = i+48;
 for (i=0; row2u[i] != '\0'; i++) g_keys[row2u[i]] = i+60;
 g_keys[' '] = -1;
 for (i=0; i<128; i++) {
  int qw = 0.5 + 0.25 * g_sampleRate / MIDI_TO_FREQ(i);
  g_qw[i] = qw;
  if (qw <= 21) {
   do {
    g_qw[++i] = --qw;   
   } while (qw > 0);
   break;
  }
 }
 if (i>124) i=124;
 for (; i<128; i++) g_qw[i] = -(i&3);

 g_quarterWaveFade = 0.5 + g_sampleRate * (0.25 / LOW_FREQUENCY_ROLLOFF);
 g_quarterWaveMax = 0.5 + g_sampleRate * (0.25 / LOW_FREQUENCY_CUTOFF);
 /*
 fprintf(stderr, "sweep speed %d; ", g_tdSweepSpeed);
 fprintf(stderr, "decay/release factor %f; ", g_tdDecayFactor);
 fprintf(stderr, "short clap decay factor %f; ", g_clapDecayFactor);
 fprintf(stderr, "short hihat decay factor %f; ", g_hhDecayFactor);
 fprintf(stderr, "aux tone decay factor %f; ", -1.0+DCV_AUX_DECAY);
 fprintf(stderr, "aux tone release factor %f\n", -1.0+DCV_AUX_RELEASE);
 */

 g_initialized = 1;
 return 0;
}



// main() handles the user interface and the startup/shutdown
int main (int argc, char *argv[])
{
 // first make sure it's run in a terminal
 if (!getenv("TERM")) execlp("xterm","xterm","-hold","-e",argv[0],NULL);

 // display the basic program info
 printf("-- JACK + ALSA MIDI instrument --\n");

 // set up the everything to work with JACK
 if ((g_client = jack_client_new(CLIENT_NAME)) == 0) {
  char name[32];sprintf(name,"%s_%d",CLIENT_NAME,getpid());// try another name
  if ((g_client = jack_client_new(name)) == 0) {// or is jackd not running?
   fprintf(stderr,"-- You must start JACK before running this program. --\n");
   return 1; }
 }
 jack_set_error_function (My_ErrorHandler);
 jack_set_process_callback (g_client, My_Process, 0);
 jack_set_sample_rate_callback (g_client, My_SampleRateChange, 0);
 jack_on_shutdown (g_client, My_JackShutdown, 0);
 g_outputPort = jack_port_register (g_client, "out",
                 JACK_DEFAULT_AUDIO_TYPE, JackPortIsOutput, 0);
 // activate the client
 if (jack_activate (g_client))
 { fprintf (stderr, "cannot activate client\n");
  return 1; }
 // find some output ports to connect to
 const char **ports;
 int i;
 ports=jack_get_ports(g_client,NULL,NULL,JackPortIsPhysical|JackPortIsInput);
 if (ports == NULL) {
  fprintf(stderr, "cannot find any playback ports (speakers?)\n");
 } else {
  for (i=0; ports[i]!=NULL; i++) {
    if (jack_connect (g_client, jack_port_name(g_outputPort), ports[i]))
      fprintf (stderr, "cannot connect output ports\n");
  }
  free (ports);
 }

 // set up an ALSA midi port
 if (snd_seq_open(&g_seqHandle, "default", SND_SEQ_OPEN_INPUT, 0) < 0) {
  fprintf(stderr, "Error opening ALSA sequencer.\n");
  return 1;
 }
 snd_seq_set_client_name(g_seqHandle, CLIENT_NAME);
 if (snd_seq_create_simple_port(g_seqHandle, CLIENT_NAME,
  SND_SEQ_PORT_CAP_WRITE|SND_SEQ_PORT_CAP_SUBS_WRITE,
  SND_SEQ_PORT_TYPE_APPLICATION) < 0) {
  fprintf(stderr, "Error creating sequencer port.\n");
  return 1;
 }
 pthread_t MIDIthread; // automate midi handling
 pthread_create(&MIDIthread,NULL,WaitOnMIDI,NULL);

 initscr(); // curses interface
 while (g_sampleRate < 1) sleep(1); // wait for JACK thread to set sampleRate

 SetUpNotes();
 while (1) {
  int gotten = getch();
  if (gotten < 0) continue;
  if (gotten == 27) {
   printw("Press ESC twice to quit.\n");
   if (getch() == 27) break;
  }
  else if (gotten == '1' || gotten == '!') {
   g_newClap = 1;
   g_clapVolume = 0.2*g_masterVolume;
  }
  else if (gotten == '`' || gotten == '~') {
   g_newHighHat = 1;
   g_hhVolume = 0.2*g_masterVolume;
  }
  else if (gotten == '-') {
   g_newCowbell = 1;
   g_cbWaveScale = 8;
   g_cbDecayFactor = 1.0 - DCV_COWBELL/g_cbWaveScale;
   g_cbVolume = 0.5*g_masterVolume;
  }
  else if (gotten == '_') {
   g_newCowbell = 1;
   g_cbWaveScale = 6;
   g_cbDecayFactor = 1.0 - DCV_COWBELL/g_cbWaveScale;
   g_cbVolume = 0.5*g_masterVolume;
  }
  else if (g_keys[gotten] > 0) {
   int qw = g_qw[g_keys[gotten]];
   if (qw > 0) {
    g_newToneDrum = 1;
    g_tdQuarterWave = qw;
    g_tdVolume = 0.8*g_masterVolume;
   }
  }
 }
 endwin();

 jack_client_close (g_client);
 return 0;
}
