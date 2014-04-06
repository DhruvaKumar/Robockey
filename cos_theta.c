#include "m_general.h"
#include "m_usb.h"
#include "m_bus.h"
#include "m_wii.h"
#include "math.h"
#include "m_rf.h"

//(Don't forget to replace Duty cycles in the timer interrupt handler!)
#define MORE_M 0.9 //Max Duty Cycle
#define MORE_L 0.75
#define MORE_LL 0.6
#define MORE_MAX 0.99 // Duty cycle of wheels while going straight!
#define LESS_M 0.45 //Min Duty Cycle
#define LESS_L 0.30
#define LESS_LL 0.25 //Very fucking less. For boundary
//Greater difference - sharper turn| Lesser diff - Puck handling easier. Trade-off. 

#define FRONT_VIC 2800 // Sum of |trans_fl|trans_c|trans_fl| to get an estimate of where to slow down before we grab the puck
#define PUCK_IN_HAND 65 // Threshold ADC value of trans_puck when PUCK_IS_IN_HAND

#define goal_1 20 //Goal offset +y direction
#define goal_2 -20 //Goal offset -y direction

#define bound_1 30 //Boundary offset in +y direction
#define bound_2 -30  //Boundary offset in -y direction

#define CHANNEL 1
#define RXADD 0x69
#define PACKET_LENGTH 10 


#define TXADD1 0x68
#define TXADD2 0x6A
//Variable initialization
volatile char buffer[PACKET_LENGTH]={0};
volatile int incomm=2;

volatile int play=0; //1=PLAY| 0=PAUSE
volatile int cX, cY, cX_prev, cY_prev=0;
volatile int stall_count=0;
//volatile float more=MORE; volatile float more_max=MORE_MAX; volatile float less=LESS;

volatile unsigned int star[12]={0};
volatile int i, j, k =0;
volatile int maxD, minD, dist, p, q, r, s=0; // p.q.r.s -> co-ordinates between which the midpoint is to be found(x2, x4)[p.q.r.s=x2.y2.x4.y4]
volatile int cx, cy, cxx, cyy =0;
volatile int count, enable, cnt,enable_1=0;
volatile int initial=0;
volatile int pmax, qmax, rmax, smax, pmin, qmin, rmin, smin, pp, qq, rr, ss=0;
volatile float theta=0;
volatile float to_angle, to_angle_1, to_angle_2, to_angle_c=0;
volatile float temp1=0;
volatile float temp_theta=0;
volatile int trans_c,trans_fl,trans_fr,trans_bl,trans_br=0,trans_puck=0;
volatile int puck_in_hand=0;
volatile float dut_cyc_B, dut_cyc_C=0;
volatile float dut_cyc=0.75;
volatile int goal_side=0;
char outcomm[PACKET_LENGTH]={0};


/*
Description:
m_red() - ON when 2 or more stars have been lost. OFF otherwise
m_green() - ON when bot is directed towards goal. (Move straight)

ADC pins used: {F0. F4. F5. F6. F7. D4} ( |trans_fl|trans_fr|trans_bl|trans_br|trans_c|trans_puck|
Timer pins used: B6.B78

Output ports:
D7 - COMM TEST (BLUE LED)

Functions:
void initt();			// Variable Initialization
void pauseMotor(); 
void compXY_theta();	// Compute current co-ordinates and orientation theta of bot w.r.t constellation
void computeADC();		// Computes the ADC values of all the photo transistors. 
void puckDetection();	// Detects puck and drives towards it. (Slows down once it's near it)
void goalDetection();	// Once the puck is in hand, the bot drives itself towards the goal. 

*/


void initt(void) //Variable Initialization
{
	/*
	Port init
	ADC init
	Timer init
	*/
	
	m_clockdivide(0);
	m_bus_init();
	m_disableJTAG(); // To use F4-F7 pins
	m_usb_init();
	m_rf_open(CHANNEL, RXADD, PACKET_LENGTH);  // Configure the RF module to listen on CHANNEL for RXADD
	sei(); //Enable global interrupt
	
	//Port init
	set(DDRD,7);    // Set as Comm test Led output
	set(DDRD,6);    // Set as PAUSE Led output
	clear(DDRD,3); // Set as input for PUCK_IN_HANDclear
	
	// Forward Drive for h bridge
	set(DDRB,0);   //  Set as output direction gate1 motorA
	set(DDRB,1);    //  Set as output direction gate2 motorA
	set(DDRB,2);     //  Set as output direction gate1 motorB
	set(DDRB,3);     //  Set as output direction gate2 motorB

	// Set this combination for the default direction as forward drive

	set(PORTB,0);
	clear(PORTB,1);
	clear(PORTB,2);
	set(PORTB,3);
	
	//set(TIMSK1,OCIE1A); // Enable Timer 1 matches ICR1A interrupt
	
	//ADC initialization
	clear(ADMUX,REFS1); //Set voltage reference for ADC as Vcc
	set(ADMUX,REFS0);
	
	set(ADCSRA,ADPS2); //Prescale ADC to 250 Khz
	set(ADCSRA,ADPS1);
	clear(ADCSRA,ADPS0);
	
	
	set(DIDR0,ADC0D); //Disabling Digital inputs for ADC pins
	set(DIDR0,ADC4D);
	set(DIDR0,ADC5D);
	set(DIDR0,ADC6D);
	set(DIDR0,ADC7D);
	set(DIDR2,ADC8D);
	
	//Timer Initialization
	set(DDRB, 6); // Set (Reg B. Bit 6) as timer output. PWM 1
	set(DDRB, 7); // Set (Reg B. Bit 7) as timer output. PWM 2
	
	set(TCCR1B, WGM13); // Set Timer 1 Mode 15 (UP to OCR1A, PWM mode)
	set(TCCR1B, WGM12);
	set(TCCR1A, WGM11);
	set(TCCR1A, WGM10);
	
	set(TCCR1A, COM1C1); // set at OCR1B. clear at rollover |Timer B.6
//CHANGE
	set(TCCR1A, COM1C0);

	set(TCCR1A, COM1B1); // set at OCR1C. clear at rollover |Timer B.7
//CHANGE
	set(TCCR1A, COM1B0);

	OCR1A=1600; //1Khz Motor
	OCR1B=0;
	OCR1C=0;
	
	
	clear(TCCR1B, CS12); // Initialize timer & Prescale /1 (Start Timer)
	clear(TCCR1B, CS11);
	set(TCCR1B, CS10);
	
	
} //End init

void pauseMotor(void)
{
	/*
	Stops the motor.
	*/
	 //play=0;	//m_green(OFF);
	set(PORTD, 6); //Switch on RED LED
	OCR1B=0; //Stop Motor
	OCR1C=0; //Stop Motor
	clear(PORTB,6); //Stop Motor
	clear(PORTB,7); //Stop Motor
} // End pauseMotor

void compXY_theta(void) //Compute current co-ordinates and orientation theta
{
	/*
	Detect the constellation. Detect the current co-ordinates from the longest/shortest distance between two stars. 
	Compute theta. Re-configure. 
	*/
	
	 //m_red(OFF);    
     //Finding max and min distance
     pmax=0; qmax=3; rmax=1; smax=4;  //p.r=(x1. y1)
     pmin=0; qmin=3; rmin=1; smin=4;  //q.s=(x2. y2)
     maxD=pow(((int)star[pmax]-(int)star[qmax]), 2) + pow(((int)star[rmax]-(int)star[smax]), 2);
     minD=maxD;
     for (i=0; i<3; i++)
     {
		 for(j=i+1; j<=3; j++)
		 {
			 dist=pow(((int)star[i*3]-(int)star[j*3]), 2) + pow(((int)star[i*3+1]-(int)star[j*3+1]), 2);
			 if(dist>maxD)
			 {
				 maxD=dist;
				 pmax=i*3; qmax=j*3; rmax=pmax+1; smax=qmax+1;
             }
			 if(dist<minD)
			 {
				 minD=dist;
				 pmin=i*3; qmin=j*3; rmin=pmin+1; smin=qmin+1;
			 }
		}   //for j
	}//for i
	
	//Check for intersection between the max & min points to find the top x.y
	if((int)star[pmax]==(int)star[pmin] || (int)star[pmax]==(int)star[qmin])
	{
		//m_red(OFF);
		p=pmax; r=rmax; q=qmax; s=smax;
		pp=p; rr=r; qq=q; ss=s;
	}
	else if ((int)star[qmax]==(int)star[pmin] || (int)star[qmax]==(int)star[qmin])
	{
		//m_red(OFF);  
		p=qmax; r=smax; q=pmax; s=rmax; 
		pp=p; rr=r; qq=q; ss=s;
	}
	else //Retain the previous co-ordinates if it can't find intersection
	{
		p=pp; q=qq; r=rr; s=ss;
		//m_red(ON);
	}
	
	//Center Point
	cx=((int)star[p]+(int)star[q])/2-512;
	cy=((int)star[r]+(int)star[s])/2-384;
	//Theta
	theta=3.14/2-atan2((int)star[s]-(int)star[r], (int)star[q]-(int)star[p]);
	cxx=1*(cx*cos(theta) - cy*sin(theta));
	cyy=1*(cx*sin(theta) + cy*cos(theta));
	//Center offset
	 cxx=cxx-65-8;
	 cyy=cyy+25-105;
	 //Center in (cm)
	 cX=-cxx/4;
	 cY=cyy/4;
	 if (initial==0) //Sets previous value for the first time. 
	 {
		 cX_prev=cX; cY_prev=cY;
		 initial=1;
	 }
	// m_usb_tx_string("  Theta_old: ");
	// m_usb_tx_int(theta*57.6);
	
	//Re-orienting theta
	if(theta*57.6>=180)
	{ 
		theta=theta-2*3.14;
	}
            /* if(theta*57.6<-180) // Why is this there?
             { theta=2*3.14-theta;
             }
             */
    theta=-theta;
} //End compXY_theta()

void computeADC(void) // Computes the ADC values of all the photo transistors. 
{
	/*
	Computes ADC values of 
	|trans_fl|trans_fr|trans_bl|trans_br|trans_c|trans_puck|
	{F0. F4. F5. F6. F7. D4}
	*/
	
	 //Trans_FL (F0)
	 clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
	 
	 clear(ADCSRB,MUX5); //Set MUX bit to F0
	 clear(ADMUX,MUX2);
	 clear(ADMUX,MUX1);
	 clear(ADMUX,MUX0);
	 
	 set(ADCSRA,ADEN); //Enable the system
	 set(ADCSRA,ADSC); //Start the conversion
	 
	 while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
	 set(ADCSRA,ADIF);// Clear the flag
	 
	 trans_fl=ADC;
	 
	 //Trans_F_RIGHT
	 clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
	 
	 clear(ADCSRB,MUX5); //set MUX bit to F4
	 set(ADMUX,MUX2);
	 clear(ADMUX,MUX1);
	 clear(ADMUX,MUX0);
	 
	 set(ADCSRA,ADEN); //Enable the system
	 set(ADCSRA,ADSC); //Start the conversion
	 
	 while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
	 set(ADCSRA,ADIF);// Clear the flag
	 
	 trans_fr=ADC;
	 
	 //TRANS_B_LEFT
	 clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
	 
	 clear(ADCSRB,MUX5); //Set MUX bit to F5
	 set(ADMUX,MUX2);
	 clear(ADMUX,MUX1);
	 set(ADMUX,MUX0);
	 
	 set(ADCSRA,ADEN); //Enable the system
	 set(ADCSRA,ADSC); //Start the conversion
	 
	 while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
	 set(ADCSRA,ADIF);// Clear the flag
	 
	 trans_bl=ADC;
	 
	 //TRANS_B_RIGHT
	 clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
	 
	 clear(ADCSRB,MUX5); //Set MUX bit to F6
	 set(ADMUX,MUX2);
	 set(ADMUX,MUX1);
	 clear(ADMUX,MUX0);
	 
	 set(ADCSRA,ADEN); //Enable the system
	 set(ADCSRA,ADSC); //Start the conversion
	 
	 while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
	 set(ADCSRA,ADIF);// Clear the flag
	 
	 trans_br=ADC;
	 
	 //TRANS_C
	 clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
	 
	 clear(ADCSRB,MUX5); //set MUX bit to F7
	 set(ADMUX,MUX2);
	 set(ADMUX,MUX1);
	 set(ADMUX,MUX0);
	 
	 set(ADCSRA,ADEN); //Enable the system
	 set(ADCSRA,ADSC); //Start the conversion
	 
	 while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
	 set(ADCSRA,ADIF);// Clear the flag
	 
	 trans_c=ADC;
	 
	 // TRANS_PUCK
	 clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
	 
	 set(ADCSRB,MUX5); //set MUX bit to D4
	 clear(ADMUX,MUX2);
	 clear(ADMUX,MUX1);
	 clear(ADMUX,MUX0);
	 
	 set(ADCSRA,ADEN); //Enable the system
	 set(ADCSRA,ADSC); //Start the conversion
	 
	 while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
	 set(ADCSRA,ADIF);// Clear the flag
	 
	 trans_puck=ADC;
	 
	 //Transmit values for debugging
	 m_usb_tx_string("  Trans_C: ");
	 m_usb_tx_int(trans_c);
	 m_usb_tx_string("  Trans_FL: ");
	 m_usb_tx_int(trans_fl);
	 m_usb_tx_string("  Trans_FR: ");
	 m_usb_tx_int(trans_fr);
	 m_usb_tx_string("  Trans_BL: ");
	 m_usb_tx_int(trans_bl);
	 m_usb_tx_string("  Trans_BR: ");
	 m_usb_tx_int(trans_br);
	 m_usb_tx_string("  Trans_PUCK: ");
	 m_usb_tx_int(trans_puck);
	 m_usb_tx_string("  Trans_FRONT: ");
	 m_usb_tx_int(trans_c + trans_fl + trans_fr);
}

void puckDetection(void)
{
	/*
	Compares the photo transistor values and drives towards the puck. 
	If it's near the puck, it slows down to grab the puck the drive it to the goal. 
	//trans_fl|trans_fr|trans_bl|trans_br|trans_c|trans_puck|
	*/
	
	//enable=0;
	clear(TIMSK1,OCIE1A); // Disable interrupt handler for TIMER1 matches ICR1A
	
	if(trans_c>trans_fl && trans_c>trans_fr && trans_c>trans_bl && trans_c>trans_br) //Puck found! Go straight!
	{
		dut_cyc_B=MORE_MAX;
		temp1=dut_cyc_B*OCR1A; //Straight! 
		OCR1B=temp1; 
		
		dut_cyc_C=MORE_MAX;
		temp1=dut_cyc_C*OCR1A;
		OCR1C=temp1; 
		m_usb_tx_string("  ||STRAIGHT||");
		
		if( trans_c + trans_fl + trans_fr > FRONT_VIC)
		{
			dut_cyc_B=MORE_L;
			temp1=dut_cyc_B*OCR1A; //Straight
			OCR1B=temp1; 
			
			dut_cyc_C=MORE_L;
			temp1=dut_cyc_C*OCR1A;
			OCR1C=temp1; 
         }
     }
	 else if ( trans_fr+trans_br > trans_fl+trans_bl) // Rotate Clockwise-
	 {
		 if(cY>bound_1 && theta*57.6 > 90) //Boundary condition beyond goal_1. Rotate anti-clockwise SLOWLY
		 {
			 dut_cyc_B=LESS_L;
			 temp1=dut_cyc_B*OCR1A;
			 OCR1B=temp1;
			 
			 dut_cyc_C=MORE_LL;
			 temp1=dut_cyc_C*OCR1A;
			 OCR1C=temp1;
			 m_usb_tx_string("  ||ANTI-CLOCKWISE||");
		 }
		 if( trans_c + trans_fl + trans_fr > FRONT_VIC || cY>bound_1) //Vicinity OR Boundary condition. Clock SLOWLY
		 {
			 dut_cyc_B=MORE_LL;
			 temp1=dut_cyc_B*OCR1A; //Clockwise
			 OCR1B=temp1;
			 
			 dut_cyc_C=LESS_L;
			 temp1=dut_cyc_C*OCR1A;
			 OCR1C=temp1;
		 }
		 else //Normal
		 {
			 enable=0;
			 dut_cyc_B=MORE_M;
			 temp1=dut_cyc_B*OCR1A; //Clockwise
			 OCR1B=temp1;
			 
			 dut_cyc_C=LESS_M;
			 temp1=dut_cyc_C*OCR1A;
			 OCR1C=temp1;
			 m_usb_tx_string("  ||CLOCKWISE||");
		 }
      }
	  else //Rotate anti-clockwise
	  {
		  if(cY<bound_2 && theta*57.6 < (-90) ) //Boundary condition beyond goal_2. Rotate clockwise
		  {
			  dut_cyc_B=MORE_LL;
			  temp1=dut_cyc_B*OCR1A;
			  OCR1B=temp1;
			  
			  dut_cyc_C=LESS_L;
			  temp1=dut_cyc_C*OCR1A;
			  OCR1C=temp1;
			  m_usb_tx_string("  ||CLOCKWISE||");
		  }
		  if( trans_c + trans_fl + trans_fr > FRONT_VIC || cY<bound_2) //Vicinity OR Boundary condition. Anti-clock SLOWLY
		  {
			  dut_cyc_B=LESS_L;
			  temp1=dut_cyc_B*OCR1A; //Anti-clockwise
			  OCR1B=temp1;
			  
			  dut_cyc_C=MORE_LL;
			  temp1=dut_cyc_C*OCR1A;
			  OCR1C=temp1;
          }
		  else //Normal
		  {
			  dut_cyc_B=LESS_M;
			  temp1=dut_cyc_B*OCR1A; //Anti-clockwise
			  OCR1B=temp1;
			  
			  dut_cyc_C=MORE_M;
			  temp1=dut_cyc_C*OCR1A;
			  OCR1C=temp1;
			  m_usb_tx_string("  ||ANTI-CLOCKWISE||");
		  }
      }
} // End puckDetection()

void goalDetection(void) //Once the puck is in hand, the bot drives itself towards the goal. 
{
	//Goal detection (Activated once puck is detected <puck_in_hand>) (Taking the range of the goal)
	to_angle_c=atan2(((goal_1+goal_2)/2-cY),(goal_side-cX)); //Angle between the goal and current position
	to_angle_1=atan2((goal_1-cY),(goal_side-cX)); //Angle between goal_1 (+y) and current position
	to_angle_2=atan2((goal_2-cY),(goal_side-cX)); //Angle between goal_2 (-y) and current position
	
	if ( (to_angle_1*57.6>0 && to_angle_2*57.6>0) || (to_angle_1*57.6<0 && to_angle_2*57.6<0) ) //If both the angles are + or - (Out of scope of goal)
	{
		to_angle= (abs(to_angle_1*57.6) < abs(to_angle_2*57.6) ) ? to_angle_1 : to_angle_2; //to_angle = whichever is lesser
	}
	else //Opposite sign (Within scope of goal)
	{
		to_angle=atan2(0,(goal_side-cX)); //Go straight
	}
		
	if (theta*57.6<=to_angle*57.6+10 && theta*57.6>=to_angle*57.6-10) // Pointing to goal. Go straight.
	{
		//Go smoothly.
		//if(!enable && dut_cyc*100<=92)
		if(!check(TIMSK1, OCIE1A) && dut_cyc*100<=92)
		{
			dut_cyc= (dut_cyc_B*100 > dut_cyc_C*100) ? dut_cyc_C : dut_cyc_B; //Take minimum of the duty cycles for the first time
			//enable=1;
			set(TIMSK1,OCIE1A); // Enable "Timer 1 matches ICR1A" interrupt
		}
		
		temp1=dut_cyc*OCR1A;
		OCR1B=temp1;
		temp1=dut_cyc*OCR1A;
		OCR1C=temp1;
		m_green(ON);
		m_usb_tx_string("  ||STRAIGHT||");
	}
	else if( theta*57.6<(to_angle*57.6-10) ) //Rotate anti-clockwise
	{
		//enable=0;
		clear(TIMSK1,OCIE1A); // Disable interrupt handler for TIMER1 matches ICR1A
		if(cY<bound_2 && theta*57.6 < (-90) ) //Boundary condition beyond goal_2. Rotate clockwise
		{
			dut_cyc_B=MORE_LL;
			temp1=dut_cyc_B*OCR1A;
			OCR1B=temp1;
			
			dut_cyc_C=LESS_LL;
			temp1=dut_cyc_C*OCR1A;
			OCR1C=temp1;
			m_usb_tx_string("  ||CLOCKWISE||");
		}
		else //Normal condition
		{
			dut_cyc_B=LESS_L;
			temp1=dut_cyc_B*OCR1A;
			OCR1B=temp1;
			
			dut_cyc_C=MORE_L;
			temp1=dut_cyc_C*OCR1A;
			OCR1C=temp1;
			m_green(OFF);
			m_usb_tx_string("  ||ANTI-CLOCKWISE||");
		}
	}
	else if ( theta*57.6>(to_angle*57.6+10) ) //Rotate clockwise
	{
		//enable=0;
		clear(TIMSK1,OCIE1A); // Disable interrupt handler for TIMER1 matches ICR1A
		if(cY>bound_1 && theta*57.6 > 90) //Boundary condition beyond goal_1. Rotate anti-clockwise
		{
			dut_cyc_B=LESS_LL;
			temp1=dut_cyc_B*OCR1A;
			OCR1B=temp1;
			
			dut_cyc_C=MORE_LL;
			temp1=dut_cyc_C*OCR1A;
			OCR1C=temp1;
			m_usb_tx_string("  ||ANTI-CLOCKWISE||");
		}
		else //Normal condition
		{
			dut_cyc_B=MORE_L;
			temp1=dut_cyc_B*OCR1A;
			OCR1B=temp1;
			
			dut_cyc_C=LESS_L;
			temp1=dut_cyc_C*OCR1A;
			OCR1C=temp1;
			m_green(OFF);
			m_usb_tx_string("  ||CLOCKWISE||");
		}
	}
}

int main(void)
{
	/* 
	while
		Read stars. 
		Initialize ADC.
		if !PUCK_IN_HAND
			Compute photo transistors & move towards puck.
		if PUCK_IN_HAND
			Go to goal with puck. 
	*/
	initt(); //Initialization (Variable. Port. ADC. Timer.)
	
 while  (m_wii_open()!=1){}
        
    while(1)
    {
        
        //clear(PORTD,6); //Switch OFF RED LED
        
		// READ STARS (Localization)
		cli();
		m_wii_read(star);
		sei();
		count=0;
		//Reading no. of detectable stars
		for(k=0;k<=3;++k)
		{
			if((int)star[3*k]==1023 && (int)star[3*k+1]==1023)
			{count++;} //Count = No. of stars lost
		}
		if(count<=1) //Enter this only if <= 1 star has been lost.
		{
			compXY_theta(); //Compute current co-ordinates and orientation theta
			computeADC(); // Computes the ADC values of all the photo transistors
			  if(!play) //PAUSE
			  {
				  pauseMotor();
			  }
			  else
			  {
				  if(!enable_1)
				  {
					  
					  
					  if(cX>=0)
					  {
						  goal_side=-115;
					  }
					  else
					  {
						  goal_side=115;
					  }
					  enable_1=1;
				  }
				  
			//Puck detection
			//trans_fl|trans_fr|trans_bl|trans_br|trans_c|trans_puck|
			
			if(trans_puck<PUCK_IN_HAND) // PUCK_NOT_IN_HAND
			{    //play=1;
				//outcomm[0]=0xB2;
				m_red(ON);
				m_green(OFF);
				//m_rf_send(TXADD1,outcomm,PACKET_LENGTH);
				//m_rf_send(TXADD2,outcomm,PACKET_LENGTH);
				puckDetection(); //Detects the puck and drives towards it. 
				
			} //if puck_NOT_in_hand
			
			else if(trans_puck>=PUCK_IN_HAND) //PUCK_IN_HAND
			{  //play=1;
			     //outcomm[0]=0xB1;
				m_red(OFF);
				m_green(ON);
				//m_rf_send(TXADD1,outcomm,PACKET_LENGTH);
				//m_rf_send(TXADD2,outcomm,PACKET_LENGTH);
				goalDetection();
			}
			/*else if(incomm==1)
			{   
				pauseMotor();
			}*/
			
			}
		}//end if (<= 1 star has been lost.)
		else //If more than 1 star has been lost:
		{   
			//m_red(ON);
			pauseMotor(); 
			p=-1; q=-1; r=-1; s=-1;
			cxx=-1; cyy=-1;
			theta=0;
		}
	
	//Debugging
    /*    
    m_usb_tx_string("X1: ");
    m_usb_tx_uint(star[0]);
    m_usb_tx_string("  Y1: ");
    m_usb_tx_uint(star[1]);
    m_usb_tx_string("  X2: ");
    m_usb_tx_uint(star[3]);
    m_usb_tx_string("  Y2: ");
    m_usb_tx_uint(star[4]);
    m_usb_tx_string("  X3: ");
    m_usb_tx_uint(star[6]);
    m_usb_tx_string("  Y3: ");
    m_usb_tx_uint(star[7]);
    m_usb_tx_string("  X4: ");
    m_usb_tx_uint(star[9]);
    m_usb_tx_string("  Y4: ");
    m_usb_tx_uint(star[10]);

	m_usb_tx_string("  P: ");
		m_usb_tx_int(p);
	m_usb_tx_string("  R: ");
		m_usb_tx_int(r);
	m_usb_tx_string("  Q: ");
		m_usb_tx_int(q);
	m_usb_tx_string("  S: ");
		m_usb_tx_int(s);
	*/
	
    m_usb_tx_string("  Theta: ");
    m_usb_tx_int(theta*57.6);
    
    m_usb_tx_string("  CX (cm): ");
    m_usb_tx_int(cX);
    m_usb_tx_string("  CY (cm): ");
    m_usb_tx_int(cY);
    m_usb_tx_string("   Count: ");
    m_usb_tx_int(count);
	m_usb_tx_string(" dut_cyc ");
	m_usb_tx_int(dut_cyc);
/*
    m_usb_tx_string("   Toangle_C: ");
    m_usb_tx_int(to_angle_c*57.6);
    m_usb_tx_string("   Toangle_1: ");
    m_usb_tx_int(to_angle_1*57.6);
    m_usb_tx_string("   Toangle_2: ");
    m_usb_tx_int(to_angle_2*57.6);
    m_usb_tx_string("   Toangle: ");
    m_usb_tx_int(to_angle*57.6);
*/
    m_usb_tx_string("\n");
   //m_wait(10);
   
   } //while (1)
}// main void()


ISR(INT2_vect) // Interrupt Handler for mRF Module
{    
    //set(PORTB, 4);
    cli();
    m_rf_read(buffer, PACKET_LENGTH);
    clear(PORTD,7); //Clear BLUE LED @Comm Test
    if(buffer[0]==0xA1) //PLAY
    {    
        play=1;
    }
    if(buffer[0]==0xA0)    //COMM TEST
    {
        set(PORTD,7);
    }
    if(buffer[0]==0xA4 || buffer[0]==0xA6 || buffer[0]==0xA7) //PAUSE (PAUSE|HALFTIME|GAME OVER)
    {
        set(PORTD,6); //Red LED ON 
        play=0;
    }
/*	 if(buffer[0]==0xB1)    //COMM TEST
	 {
		 incomm=1;// Other bot has found the puck
		 play=0;
	 }
	 if(buffer[0]==0xB2)    //COMM TEST
	 {
		 incomm=2; // Other bot is looking for the puck
		 play=1;
	 }
	 */
    sei();
}

ISR(TIMER1_COMPA_vect)
{
	//if(enable)
	//{
		cnt++;
		if(cnt>=80) // Increment in steps of cnt ms. (250ms=0.25s)
		{
			 cnt=0;
			 dut_cyc=dut_cyc+0.01;
			 if(dut_cyc>=0.98)
			 {
				 //enable=0;
				 clear(TIMSK1,OCIE1A); // Disable interrupt handler for TIMER1 matches ICR1A
			 }
		}
	//}
}
/*
ISR(TIMER1_COMPA_vect) //Stalling condition
{
    //Prevent stalling (If position is almost same (within 5cm) for >1s set PWM LESS 0 PWM MORE 0.99)
    if( abs(cX_prev-abs(cX))<5 && abs(cY_prev-abs(cY))<5 )
    {
        stall_count++;
        if(stall_count>=1000) //1 sec (time period of OCR1A=1ms)
        {
            more_max=0.99; //Override duty cycle 
            more=0.99;
            less=0;
            m_usb_tx_string(" |Stalling!| ");
        }
        
    }
    else //Position changed. No stalling.
    {
        more=MORE; //Replace with default values
        more_max=MORE_MAX; 
        less=LESS;
        stall_count=0;
        cX_prev=cX; //New co-ordinates to check with
        cY_prev=cY;
        m_usb_tx_string(" |Moving!| ");
    }
}
*/

//Condition for puck being just besides the wheel. PWMLESS=10 


/*
Changes made:
 
Straight_vicinity = LESS_L -> LESS_M.
Boundary condition in PUCK FIND.
TIMSK bit instead of enable
*/		
/* Communication protocol

  Initially both the bots are in puck find mode.
  The message consists of 1 parameter

  0XB1- I Have the puck
  0XB2- I dont have the puck
  
  As long as abot receives 2 it runs puckfind()
  Once a bot finds the puck it transmits the 1 at which point the other bot just stops where it was for today
  Once it loses the puck the other bot along with this bot goes into puckfind mode.
  
			  
  */
