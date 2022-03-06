/************************************************************************************************
  2019.12.15 22:45
  IBT demo radio telescope sketch with UDS connection to Radio-SkyPipe.
  The UDS command processor came from RadioSky web site.  Added assorted mods.
        Bruce Randall NT4RT  July 10, 2018,  Sept 27, 2018
        Oct 10, 2018  Major I/O schuffle and TIMER1 driven tone process
        Oct 11, 2018 ADC driven by TIMER2 IRQ for accurate timing.
        Oct 12, 2018 added full interpolation to PWR table lookup
        Oct 14, 2018 added "volitile" to all IRQ variables. Removed do nothing code
        Feb 15, 2019 change to external 3.3V reference for ADC.
        Feb 23, 2019 Added compile time option of TI ADS1015 ADC.
        Feb 25, 2019 new LUT in .h file 510mV span at AD8318
        Mar 10, 2019 Change to use I2C test to select ADS1015
        Jun 10, 2019 Change for HW Audio path. D7 now high to select Detector Audio.
        Jul 23, 2019 Add AutoNul on command from push button.
        Sep 20, 2019 START MAJOR CHANGE to 15 bits instead of 14.  Faster Autonull
        Dec 03, 2019 encoder & offset changes
        Dec 15, 2019 Calibration of tone routine
        Mar 05, 2022 no code changes.  Added comments for ADS1115 ADC
        
  In UDS PUSH mode, data is sent every 100 milliSeconds.
  in UDS POLL mode, Data request should not be closer than 100 milliSeconds
  WARNING:  This sketch does NOT fully decode SkyPipe UDS commands.  Any added commands
  to UDS could cause trouble!!!
  Tau Filter Range is 0.1 .. 0.2 .. 0.4 .. 0.8 .... 25.6 Seconds Equiv RC ( 0.1S * 2^N )

  WARNINGS on Timer-Counter usage:
  Timer0  8 bit   Orignal usage Sketch timing & PWM 5 & 6
  Timer1  16 bit  Non-standard!  16 bit tone generation  NO PWM 9 & 10 or Servo Functions!!!
  Timer2  8 bit   Non-standard!  Does timing for ADC    NO tone() function or PWM 3 & 11

  Normal Full Scale signal range  in all processes is 0 to 32767  9/20/19
***************************************************************************************************/

#define debug false             // Set true to debug with a terminal in place of SkyPipe.
// ************** WARNING!  SkyPipe will NOT work if debug is true. IT CRASHES!!!  REALLY REALLY BAD!!!

#include <EEPROM.h>             // Allow EEPROM usage
#include <Wire.h>               // I2C drivers used by ADS1015 12 bit ADC or ADS1115 16 bit ADC

#include "Exp_Lookup.h"         // Table to convert log detector response to linear temperature responce.

// Define  MCU pins ********** Schuffled for TIMER1 tone output Oct 10, 2018
//                        0     // Serial for IDE
//                        1     // Serial for IDE
//                        2     // DIO, can be IRQ input **NOT USED**
#define EncoderPinA       3     // Input with pullup  Also Port D mask 0x08 
#define EncoderPinB       4     // Input with pullup Also Port  D mask 0x10
#define Meter_pin         5     // PWM output for analog meter.    
#define Offset_pin        6     // PWM for offset voltage.
#define DetSel            7     // Output. High Selects Audio path for detector.  Changed Jun 10, 2019 
#define EncoderPush       8     // Input from push switch on encoder  
#define ToneOutAF         9     // Tone Warning: This prevents pins 9 and 10 PWM
#define AudioSelPush      10    // Inputfrom push button switch 
#define LUT_pin           11    // Input.  High for LUT meter output, low for linear.
#define FW_T_pin          12    // Output Pin wiggles at ADC routine.  Test Point ONLY!!
#define LED_Pin           13    // LED on this  pin on UNO PWB.     Used as test point.
//                        14    // Used as Analog 0 input to internal Arduino 10 bit ADC
//                        15    // GPIO or A1           **NOT USED**
//                        16    // GPIO or A2           **NOT USED**
#define AutoNulPin_L      17    // Was A3.  Now Dig Input. Hold low to seek half scale on adcFiltOut15. Tunes offset PWN to null. 
//                        18    // Used as I2C was A4
//                        19    // Used as I2C was A5

#define DetectorV         0     // Amalog Input A0

#define EncA_Mask         0x08 // Bit on port D
#define EncB_Mask         0x10 // Bit on port D

// Timing stuff sets ADC and output sample rates
#define TMR2_Period       249   // OCR value for 4.00mS cycle.  1 / 16E6 * 256 * (249+1) = 4.00mS
#define Ticks             25    // This is the number of adc reads per out sample in UDS PUSH mode
//  4.00mS thru loop * 25 passes = 100mS
int count100mS = 0;             // counter for 50mS and 100mS internal tasks and 100mS output

// Stuff for ADS1015 ADC
#define ADS_Adr 0x48            // default I2C address of ADS1015 A/D converter.  or ADS1115 also
                                // ADS sample rate driven by timer. Setup for 250 Hz
#define ADS_Control 0x8B43      // ADS1015: ADS Start, Diff in 0:1,  0.5V span, 490 SPS, Triggered conversion.  Actaul=250 SPS.
// #define ADS_Control 0x8BC3   // ADS1115 16 bit ADC:  same above except 475 SPS.   
boolean i2c_ADC_OK = false;     //Set to true if ADS1015 is found in initialize.  if false use onboard ADC10

boolean poll = true;            // if true then data is polled by RSP using a GETD command
int stat = 0;                   // -1 = we were just stopped by a KILL command 0 = startup state
// 1 = INIT rcvd 2 = Ready to Go 3= Running

byte audioSel = 0;              // Select Audio Path.  Possible values below.  Saved in EEPROM
#define No_AF   0                   // 0 = no audio
#define Tone_AF 1                   // 1 = tone audio
#define Det_AF  2                   // 2 = detector audio
#define DetAFOn HIGH                // port pin "DetSel" to enable detector AF Amp
#define DetAFOff LOW                // port pin "DetSel" to disable detector AF Amp
byte audioSelZ   = 0;           // previous state of audioSel

#define Pitch700 11427          // Load to make 700Hz tone with TIMER1 for beeps. Calc = 16E6/700/2   
#define InitTone 3200           // Zero level tone frequency, Hz * 16.  Must be > 1955 !!        
#define K_T1_FP  128000000      // Freq to Period for 32767 data = about 2048 Hz 
                                // K_T1_FP = 32767 * 16E6Hz / 2048Hz / 2 = 128E6 

volatile unsigned int t1Period = Pitch700; // Used in TIMER1 tone generation

int sw_Count = 0;                 // counts 100mS ticks for EEPROM write command
#define SW_Detect 12              // number of ticks to activate EEPROM write 

volatile int adcBox = 0;            // holds 10 or 12 bit ADC data from IRQ routine
volatile boolean adcFlag = false;   // Set by timer 2.  True when it is time to run ADC
int adcFiltOut15 = 0;               // Output of IIR filter in ADC routine 15 bits wide positive value.
#define HalfScale15 16383           // for half scale test of adcFilt15

#define ADCFiltK_Sel 4              // value 4 gives 4.0mS *(2^4) = about 64mS RC

#define TauFilK_Min 1               // lowest safe value 1 gives 50mS *(2^1) = about 100mS RC 
#define TauFilK_Max 9               // highest value 9 gives 50mS *(2^9) = about 26 Sec
#define TauFilK_PWM 25              // calc from floor(255/(Max-Min)), slightly lower is OK (displa filt setting)
byte tauFilK_Sel = TauFilK_Min;     // Range limit MUST be checked! saved in EEPROM

int dataBus15 = 0;                  // main data for output devices.  Data 15 bitswide positive value

int incomingByte;                   // from serial port
byte af_Sw, af_Sw_Z = HIGH;         // Audio Sel & previous state of it

boolean encoderA, encoderB, encoderZ = 1;  //"Z" is previous state of encoderA
int offset_Set_i = 512;             // 0 ... 1020  saved in EEPROM & PWM as byte after div 4    scaled Dec 02, 2019 for encoder feel.  
#define OffsetMax 1020              // Max value for offset as 10 bit integer
byte eeData = 0;                    // used in EEPROM process
#define EEADR_Key 0                 // start of EEPROM
#define EE_Key_Value 0x52           // Value in key to establish EE data is valid
#define EEADR_Ofst 1                // EE Address of offset
#define EEADR_Filk 2                // EE Address of filter K
#define EEADR_ASel 3                // EE Address of Audio Select

// ***********************************************************************************
// ************************** Start Programme ****************************************
void setup() {                      //  UDS stat, poll are inialized in assignment
  InitPort();                       // Setup all I/O ports
  Serial.begin(9600);               // connect to the serial port
  analogReference(EXTERNAL);        // use 3.3V supply as reference.  Hardware connection needed!  2019.02.15
  analogRead(0);                    // Dummy read to clear ADC.
  while (!Serial) ;                 // wait for serial port to connect. Needed for native USB port only.

  Wire.begin();
  Wire.beginTransmission (ADS_Adr);       // Test for ADS1015 or ADS1115 present.  If present use it!
  if (Wire.endTransmission () == 0) {
    i2c_ADC_OK = true;                    // Set flag for ADS1015 found.  Was defined as false.
    delay(2);                             // needed or not ???
    write_ADS( ADS_Adr,  ADS_Control);    // kick off ADS1x15 first conversion
    delay(4);                             // wait 4mS for first ADS1x15 conversion to complete
  }

#if debug
  Serial.print("^^1002 Arduino UDS ");
  Serial.write(255);
  Serial.println("");
#endif
  GetEE();
  TIMER_setup();                // Setup TIMER1 IRQ for tone gen. Setup TIMER2 IRQ driven ADC.
  delay(100);                   // may not be needed, but causes no harm
}                               // end of Setup
//***********************************************************************************
//***********************************************************************************
// TIMER1 IRQ for tone generation
ISR(TIMER1_COMPA_vect)          // timer compare interrupt service routine
{
  OCR1A = t1Period;             // tone vaue => counter update
}

//***********************************************************************************
// TIMER2 IRQ for IRQ driven ADC.  IRQ is every 4mS.  Process takes 115uS for uP 10 bit ADC.
ISR(TIMER2_COMPA_vect) // timer compare interrupt service routine
{
  digitalWrite(LED_Pin, HIGH);          // test point to observe timing
  adcFlag = true;                       // ADC data is ready
  digitalWrite(LED_Pin, LOW);           // test point to observe timing
}
//***********************************************************************************
//***********************************************************************************
void loop() {
  /**********************************************************************************
    If we are pushing the data to RSP then we need to establish our timing for
    sending new data.  Here we are doing a delay of 100ms from a timer to get a
    sample rate of 10 samples per second.
  ************************************************************************************/
  // * * * * * * * * * * * * * * Task done every 4 mSec * * * * * * * * * * * * * *
  // Timing is set ADC_Process which waits for TIMER2 to trigger ADC.
  digitalWrite(LED_Pin, HIGH);          // test point to observe timing
  ADC_Process();       // get ADC data from IRQ and filter. Result in IIR filter
  digitalWrite(LED_Pin, LOW);           // test point to observe timing 
  CmdProcess();        // check for command from Radio SkyPipe
  ENC_Process();       // check for encoder knob changes & process

  // Check for timer task queue up or timeout.
  count100mS++;                           // counter is NEVER 0 after ++
  // * * * * * * * * * * * * * * Task done every 50mSec * * * * * * * * * * * * * *
  if ((count100mS == (Ticks / 2 + 1 )) ||
      (count100mS == 1))     {            // every 50mS updates
    if (digitalRead(LUT_pin) == HIGH) {   // Lookup table select input pin
      dataBus15 = GetPwrData();           // Change LOG data to PWR data, if switch set.
    }  //x LUT_pin
    else   dataBus15 = adcFiltOut15;

    dataBus15 = TauFilter(dataBus15);     // do "integrator" RC filter time step
    Set_Tone();                           // 50mStone update needed for smoothness
  }

  // * * * * * * * * * * * * * * Task done every 100mSec * * * * * * * * * * * * * *
  if (count100mS >= Ticks) {              // task done on the 100mS tick
    count100mS = 0;
    ReadSwitches();                       // read push button switches
    if (digitalRead(AutoNulPin_L) == LOW) // if AutoNul switch pushed
      autoNul();                          //    
    Set_PWM();                            // update PWM's outputs
    if (( !poll ) && (stat == 3)) {       // time to PUSH data if PUSH mode
      GETD();                             // send data to PC => SkyPipe
    }
    //   Serial.println(adcBox);          // Debug and test code.
  }
  // * * * * * * * * * * * * * * End of Task done every 100mSec
}    //**** end of main "loop"

// *****************************************************************************************
// ************** functions used by main programe ******************************************

//*****************  command processor *******************
void CmdProcess() {
  while (Serial.available() > 0) { // very long while loop.
    incomingByte = Serial.read();  // read the oldest byte in the serial buffer:

    // **** if it's a K we stop (KILL):
    if (incomingByte == 'K') {
      DumpChar(3);  //GET PAST THE REST OF THE WORD by Reading it.
      stat = -1;
#if debug
      Serial.println("^^1002 DEAD"); // Just for troubleshooting
#endif
    }
    // **** if it's an I run the INIT code if any
    if ((incomingByte == 'I') && (stat == 0)) {
      DumpChar(3);  // GET RID OF 'NIT'
      stat = 1 ;
#if debug
      Serial.println("^^1002 INITIALIZED ");
#endif
    }
    // **** if it's an L RSP will have to POLL for data
    if (incomingByte == 'L') {
      DumpChar(1); // GET RID OF 2nd 'L' in POLL
      poll = true;
#if debug
      Serial.println("^^1002 POLLING ");
#endif
    }
    //**** if it's an H sets it to push.  Arduino will PUSH data.
    if (incomingByte == 'H') {
      poll = false;
#if debug
      Serial.println("^^1002 PUSHING ");
#endif
    }

    //**** if it's a C then Radio-SkyPipe is requesting number of CHANnels
    if (incomingByte == 'C') {
      DumpChar(3);  // GET RID OF 'HAN'
      // change the last digit to = digit of channels of data (ex. 1)
      delay(10);
      Serial.print("^^20131");
      Serial.write(255);              // print result;
      stat = 2;                       // ready to go
#if debug
      Serial.println("");
#endif
    }

    //****  if it's an "A" means STAT was requested so send UDS ready message
    if (incomingByte == 'A' ) {
      DumpChar(1);                    // GET RID of final 'T'
      Serial.print("^^1001");
      Serial.write(255);              // print result
      stat = 3;
#if debug
      Serial.println("");
#endif
    }

    //***** if it's an D we should send data to RSP:
    if ((incomingByte == 'D') && poll && (stat == 3) ) {
      GETD() ;
#if debug
      Serial.println(" DATA REQUEST RECEIVED ");
#endif
    }

    if (stat == -1) stat = 0;     // clear kill state automatically
  }   //**** End of "while (Serial.available() > 0)"
  // we are finished processing any incoming commands from the PC
}     //**** end of function cmdProcess

/**********************************************************
     Initial setup of all I/O ports
*/
void InitPort() {
  pinMode(ToneOutAF, OUTPUT);
  T1_Tone_Off();                      // turn off TIMER1 output of tone

  // **** Set up rotary encoder pins
  pinMode(EncoderPinA, INPUT_PULLUP);
  pinMode(EncoderPinB, INPUT_PULLUP);
  pinMode(EncoderPush, INPUT_PULLUP);
  
  pinMode(LUT_pin, INPUT_PULLUP);
  pinMode(AudioSelPush, INPUT_PULLUP);
 
  pinMode( AutoNulPin_L, INPUT_PULLUP);
  
  digitalWrite(DetSel, DetAFOff);     // preset to disable state, stop noise burst at powerup ch 2019.6.10
  pinMode(DetSel, OUTPUT);            // Selects detector audio off at power up 
  pinMode (FW_T_pin, OUTPUT);
  digitalWrite(FW_T_pin, LOW);        // test point for firmware timing.
  
  // analogReference (EXTERNAL);        // select 3.3V reference done in calling code
  // analogRead (0);
  pinMode(LED_Pin, OUTPUT);
}

/**********************************************************
   SETUP TIMERS 1 and 2 for special use
   WARNING:  PWM pins 3, 9, 10, and 11 no linger work.  SERVO library no longer works !!!   
*/
// Set up TIMER1 for High resolution tone .
void TIMER_setup() {
  // Setup timer IRQ for tone generation.
  // WARNING: This steals Timer1 from PWM's on Pins 9 and 10.  Also breaks servo library.
  noInterrupts();               // disable all interrupts
  TCCR1A = 0;
  TCCR1B = 0;
  TCNT1 = 0;

  OCR1A = Pitch700;             // compare register
  TCCR1B |= (1 << WGM12);       // CTC mode
  TCCR1B |= (1 << CS10);        // 1x prescaler

  TIMSK1 |= (1 << OCIE1A);      // enable timer compare interrupt
  TCCR1A |= (1 << COM1A0);      // pin 9 gets timer toggle output

  //   Set up TIMER2 for ADC interupt
  // WARNING: This steals Timer2 from PWM's on Pins 3 and 11.  Also breaks tone() function
  TCCR2A = 0;
  TCCR2B = 0;
  TCNT2  = 0;
  OCR2A  = TMR2_Period;         // compare register
  TCCR2A |= (1 << WGM21);       // CTC mode
  TCCR2B |= ((1 << CS21) | (1 << CS22));        // 256x prescaler & start clock
  TIMSK2 |= (1 << OCIE2A);      // enable timer compare interrupt
  interrupts(); // enable all interrupts
}

/**********************************************************
   This is where data is fetched and sent on to RSP.
*/
void GETD() {
  Serial.print("#0");         // # followed by channel number of data
  Serial.print(dataBus15);    // Scale OK,  Fullscale = 32767
  Serial.write(255);
  Serial.print("^^3001");     // This tells RSP to time stamp it
  Serial.write(255);          // all commands end with this character.
#if debug
  Serial.println("");
#endif
  return;
}

/*********************************************************************
   This pulls characters from serial port buffer & throws them away.
   It is needed because we decode only one character of commands.
*/
void DumpChar(int charCount) {
  int loops;
  for ( loops = 1; loops <= charCount; loops++ ) {
    delay(10);
    incomingByte = Serial.read();
  }
  incomingByte = 0;
}

/****************************************************************************************
   ADC_Process to global output variable adcFiltOut15.  Output full scale = 32736.
   Selected ADC runs here after flag from timer 2 kicks it off.
   Gets data from adcBox, and scales as needed for adcFiltOut14 global.
   Filter is 1 pole IIR low pass with shifts making filter K.  About 64mS RC
   Process takes ### uSec after adcFlag becomes true.

   Waits here until flaq from ADC IRQ Process.  NOT BEST BUT WORKS !!!
   .. Changed Internal calcs to 32 bit to avoid round off errors.        July 29, 2018
   .. Changed to TIMER2 IRQ timing of ADC.                               Oct 11, 2018
   .. changed to TIMER2 kicks off ADC here.  ADS1015 I2C NOT OK in IRQ!  Feb 23, 2019
*/
void ADC_Process() {
  long adcFiltInL;                          // IIR filter processes ADC reads to smoothed value
  static long adcFiltMemL;                  // Memory for IIR filter

  //digitalWrite(FW_T_pin, HIGH);             // # test point for firmware timing.
  while (!adcFlag);                         // WAIT timer says "run ADC", (adcFlag == true)
  adcFlag = false;                          // clear for next timer event.
  digitalWrite(FW_T_pin, HIGH);             // # test point for firmware timing.
  if (i2c_ADC_OK) {                         // Use external I2C ADC
    adcBox = read_ADS ( ADS_Adr);           // get data from LAST conversion
    adcBox = (adcBox + 0x8000) >> 1;        // this may need work.  0x7FF8 or 32760 full scale
    write_ADS( ADS_Adr,  ADS_Control);      // kick off NEXT ADS1015 conversion
  }
  else {                                    // Use On-chip 10 bit ADC
    adcBox = (analogRead(DetectorV)) << 5;  // 10 bit to 15 bit unsigned 0x7FE0 or 32736 full scale
  }

  //******   Now filter with one pole IIR low pass at about 64mS equiv RC *******************
  adcFiltInL = (long)adcBox;                // get ADC data 32736 full scale
  adcFiltInL = adcFiltInL << 15;            // scale by 2^15 to use long data type
  adcFiltInL -= adcFiltMemL;                // get delta step in
  adcFiltInL = adcFiltInL >> ADCFiltK_Sel;  // fixed filter K for ADC done with a shift
  adcFiltMemL += adcFiltInL;                // filtered output in analogFilOut
  adcFiltOut15 = (int)(adcFiltMemL >> 15);  // scale back to fit in int data type
  digitalWrite(FW_T_pin, LOW);              // # test point for firmware timing.
}
/******************************************************************************************
  Takes input from global analogFiltOut.  Full Scale here is 32767 input and output.
  The exponential output from log input is done with a 1024 length look up table.
  uses interpolation for full 15 bit operation.
*/
int GetPwrData() {
  int indx, tOut, tOut2, delta, out, testH;
  indx = (adcFiltOut15 >> 5);                       // 0 ... 1023 here is index
  if (indx < 0)    indx = 0;                        // stay in table!!
  if (indx > 1023) indx = 1023;                     // Table in PROGMEM space
  tOut  = pgm_read_word_near(&lookup[indx]);        //  "= lookup[indx]" DOES NOT WORK
  tOut2 = pgm_read_word_near(&lookup[indx + 1]);
  delta = tOut2 - tOut;                             // slope info
  testH = adcFiltOut15 & 0x1F;                      // get  lsb's for interpolate test
  testH *= delta;
  testH = testH >> 5;
  out = tOut + testH;
  return out;
}

/****************************************************************************************
   TauFilter is basic RC time constant for Radio Telescope. NOTE STATIC MEMORY!!!
   Output full scale = 32736
   Main loop will normally run this about every 50mS.
   Internal calcs are 32 bit to reduce round off errors,  Created Sept 27, 2018
*/
int TauFilter(int input) {
  long rcFiltIn;
  static long rcFiltMem;              // Memory for IIR filter
  rcFiltIn = input;                   // put input in 32 bits
  rcFiltIn = rcFiltIn << 15;          // scale by 2^15 to use long data type
  rcFiltIn -= rcFiltMem;              // get delta step of input
  rcFiltIn = rcFiltIn >> tauFilK_Sel; // Divide it by typical 32 for filter K of 1/32.
  rcFiltMem += rcFiltIn;              // filtered output in analogFilOut
  return (int)(rcFiltMem >> 15);        // scale back to fit in int data type
}

/****************************************************************
  Read shaft encoder and process changes.    Changed  02 Dec 2019
  Input Pin Notes added 25 Nov 2020
  Changes offfset value for ADC preamp via a PWM
  If knob is pushed in,  Changes IIR filter time constant.
  Runs every 4mS or so. Changes with ADC selection
  Encoder inputs have 30K to 50K pullups in uP enabled.  Contacts to Gnd.
  Possible DeBounce:
  Enc ---- 3K3 Res ---- 0.033u to Gnd ----- Port Pin.
  Give 100uS / 1000uS for RC Lo vs RC Hi.  May need 0.1u???
*/
void ENC_Process() {                                
  byte enc_port;
  enc_port = PIND;                         // simultainious pin read                 
 if (enc_port & EncA_Mask) encoderA = true; else encoderA = false;
 if (enc_port & EncB_Mask) encoderB = true; else encoderB = false;
 if (encoderA != encoderZ)     {                // detect any edge change on A
    if (encoderB != encoderA) {   // EncoderB sorts CW vs CCW 
     // Decrease offset or filter K
      if ( digitalRead(EncoderPush) == HIGH)    // NOT pushed
        offset_Set_i--;                           // Change offset down
      else tauFilK_Sel--;                       // Change to shorter RC time equiv
    }
    else  {
      // Increase offset or filter K
      if ( digitalRead(EncoderPush) == HIGH)    // NOT pushed
        offset_Set_i++;                           // Change offset up
      else tauFilK_Sel++;                       // Change to longer RC time equiv
    }

    // Check limits here for offset size and filter K size
    // Both are byte size values
    if ( offset_Set_i < 0 )   offset_Set_i = 0;
    if ( offset_Set_i > OffsetMax ) offset_Set_i = OffsetMax;

    if (  tauFilK_Sel < TauFilK_Min) tauFilK_Sel = TauFilK_Min;
    if (  tauFilK_Sel > TauFilK_Max) tauFilK_Sel = TauFilK_Max;
  }                                             // end of detect edge
  encoderZ = encoderA;            // to catch state change NEXT time
}                                 // end of ENC_Process

/****************************************************************
  Read push button switches and process changes.  In 100mSec loop.
  Note that a pushed switch is LOW !!!
  AF routing switch.
*/
void ReadSwitches() {
  byte i;
  af_Sw = digitalRead(AudioSelPush);
  if ( (af_Sw == LOW) && (af_Sw_Z == HIGH)) {   // if High to Low edge detected on pin
    audioSelZ = audioSel;                       // to restore after EEPROM write
    audioSel++;
    if (audioSel > Det_AF) audioSel = No_AF;
  }                                             //  x if High to Low edge detected
  af_Sw_Z = af_Sw;                      // setup for NEXT edge detect

  if (af_Sw == HIGH) sw_Count = 0;      // for EEPROM
  if (af_Sw == LOW) {                   // Switch pushed ?
    sw_Count++;
    if (sw_Count > SW_Detect) {         // if a Long Push then do EEPROM write
      audioSel = audioSelZ;             // so EEPROM write dowes not change state
      PutEE();
      for (i = 0; i < 3; i++) {         // Make 3 beeps
        t1Period = Pitch700;            // Need to set pitch for 700 Hz here
        T1_Tone_Off();                  // turn off TIMER1 output of tone
        delay(100);                     // blocking of ADC IRQ by delay is OK here.
        T1_Tone_On();                   // turn off TIMER1 output of tone
        delay(300);                     // blocking of ADC IRQ by delay is OK here.
        T1_Tone_Off();                  // turn off TIMER1 output of tone
      }                                 // x Make 3 beeps
      while (af_Sw == LOW) {            // wait for pin HIGH to exit (Push released)
        af_Sw = digitalRead(AudioSelPush);
      }                                 // x wait for HIGH to exit
    }                                   // x if a Long Push then do EEPROM write
  }                                     // x Switch pushed ?
}                                       // x function ReadSwitches()

/****************************************************************
  Set Tone Pitch from Global dataBus15 value of 32736 Full Scale
  possible range of about 200 to 2200Hz.
  Also Selects audio path. 
*/
void Set_Tone() {
  long toneFreq16L, tempIL;
  switch (audioSel) {                         // Do audio path select first
    case No_AF:
      T1_Tone_Off();                          // turn off TIMER1 output of tone
      digitalWrite(DetSel, DetAFOff);         // Power down AF amp
      break;
    case Tone_AF:
      digitalWrite(DetSel, DetAFOff);         // Power down detector to AF amp path
      toneFreq16L = (long)dataBus15 + InitTone;    // make 32 bit & add offset freq
      tempIL = K_T1_FP / toneFreq16L;         // 32 bit calc needed
      t1Period = (unsigned int)tempIL;        // back to 16 bits for timer.  TimerIRQ loads this into timer reg
      T1_Tone_On();
      break;
    case Det_AF:
      T1_Tone_Off();                          // turn off TIMER1 output of tone
      digitalWrite(DetSel, DetAFOn);          // Power up detector AF amplifier
      break;
  }
}
/****************************************************************
  Enable timer1 tone output.
*/
void T1_Tone_On() {
  pinMode(ToneOutAF, OUTPUT);     // turn on TIMER1 output of tone
}

/****************************************************************
  Disable timer1 tone output.
*/
void T1_Tone_Off() {
  pinMode(ToneOutAF, INPUT);      // turn off TIMER1 output of tone
}

/****************************************************************
  Set PWM from Output data value.
*/
void Set_PWM() {
  int tempI;
  if ( digitalRead(EncoderPush) == HIGH)  {             // NOT pushed, Output = PWM of signal
    analogWrite(Meter_pin, dataBus15 >> 7);            // 8 bit data to PWM
  }
  else  {                                               // Knob pushed, Output filter K displayed
    tempI = ( tauFilK_Sel - TauFilK_Min) * TauFilK_PWM;      // Display & filt OK
    analogWrite ( Meter_pin, tempI );                   // shows log2(filt K)
  }
  analogWrite ( Offset_pin, (byte)(offset_Set_i >>2) );   // Scale back to byte for PWM
}

/****************************************************************
  Gets EEPROM data.  If key is set, puts data in proper variables.
  Must match PutEE.
*/
void GetEE() {
  eeData = EEPROM.read(EEADR_Key);
  if (eeData == EE_Key_Value) {                 // if there is data, get it
    offset_Set_i = ((EEPROM.read(EEADR_Ofst)) << 2);       //mult x 4 for 1020 FS. from byte
    tauFilK_Sel  = EEPROM.read(EEADR_Filk);
    if ( tauFilK_Sel < TauFilK_Min) tauFilK_Sel = TauFilK_Min;  // Check.  Wrong value is a mess!
    if ( tauFilK_Sel > TauFilK_Max) tauFilK_Sel = TauFilK_Max;
    audioSel = EEPROM.read(EEADR_ASel);
  }
}

/****************************************************************
  Puts data in EEPROM.  Includes key.
  Must match GetEE.
*/
void PutEE() {
  EEPROM.write(EEADR_Key,  EE_Key_Value);
  EEPROM.write(EEADR_Ofst, (byte)(offset_Set_i >>2));       //divide by 4 so it fits in byte
  EEPROM.write(EEADR_Filk, tauFilK_Sel);
  EEPROM.write(EEADR_ASel, audioSel);
}

//**************************** TI ADS1015 I2C drivers ***********************************************
// WARNING:  These two functions are NOT reentrant!!!  Can't be inside timer IRQ or lockas up ???
// They are OK in main loop
// ****  Write word to ADS1015 configuration/command register  ****
static volatile void write_ADS( uint8_t i2C_Adr, uint16_t value) {
  Wire.beginTransmission(i2C_Adr);
  Wire.write((uint8_t)1);                       // Reg 1 is configuration data
  Wire.write((uint8_t)(value >> 8));            // Send Hi Byte
  Wire.write((uint8_t)(value & 0xFF));          // Send Lo Byte
  Wire.endTransmission();
}

// ****   Read word from ADS1015 conversion resuilt register  ****
static volatile uint16_t read_ADS ( uint8_t i2C_Adr) {
  Wire.beginTransmission(i2C_Adr);
  Wire.write((uint8_t)0);                     // Reg 0 is conversion data
  Wire.endTransmission();
  Wire.requestFrom(i2C_Adr, (uint8_t)2);      // gets 2 bytes
  return ((Wire.read() << 8) | Wire.read());
}

/*********************************************************************************************************
* Added July 23, 2019  Modified Sept 24, 2019, Dec 2, 2019.    
* Called from 100mS task if AutoNul button pushed to request calibration.  
* Evaluates Filtered Scaled ADC value  and adjusts Offset PWM up or down as needed to center ADC.      
* I/O through global variables                */ 
void autoNul() { 
  int nullErr = adcFiltOut15 - HalfScale15;         // Delta Null Error.  Range about +/-16383
  nullErr = nullErr >> 7;                           // Range now +/-127   
  offset_Set_i -= nullErr;
// Check limits here for offset size.  Prevent unsigned byte overflow or underflow
    if ( offset_Set_i < 0 )    offset_Set_i = 0;
    if ( offset_Set_i > OffsetMax ) offset_Set_i = OffsetMax;
}
// ****************** end of programme ***********************************************************
