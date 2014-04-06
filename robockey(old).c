#include "m_general.h"
#include "m_usb.h"
#include "m_bus.h"
#include "m_wii.h"
#include "math.h"
#include "m_rf.h"

#define MORE 0.99 //Max Duty Cycle
#define LESS 0.90 //Min Duty Cycle


#define goal_1 -5 //Goal offset +y direction
#define goal_2 -40 //Goal offset -y direction

#define CHANNEL 2
#define RXADD 0X68
#define PACKET_LENGTH 10 

volatile char buffer[PACKET_LENGTH]={0};
volatile int play=0; //1=PLAY| 0=PAUSE

/*
m_red() - ON when 2 or more stars have been lost. OFF otherwise
m_green() - ON when bot is directed towards goal. (Move straight)

ADC pins used: F1.F4.F5.F6.F7
Timer pins used: B6.B7

Output ports:
D7 - COMM TEST (BLUE LED)
*/

int main(void)
{
    m_clockdivide(0);
    m_bus_init();
    m_usb_init();
	m_rf_open(CHANNEL, RXADD, PACKET_LENGTH);  // Configure the RF module to listen on CHANNEL for RXADD
	sei(); //Enable global interrupt
	
	unsigned int star[12]={0};
    int i, j, k =0;
    int maxD, minD, dist, p, q, r, s=0; // p.q.r.s -> co-ordinates between which the midpoint is to be found(x2, x4)[p.q.r.s=x2.y2.x4.y4]
    int cx, cy, cxx, cyy, cX, cY=0; 
	int count=0;
    int pmax, qmax, rmax, smax, pmin, qmin, rmin, smin, pp, qq, rr, ss=0;
    float theta=0;
    float to_angle, to_angle_1, to_angle_2, to_angle_c=0;
    float temp1=0;
	float LESS2=0;
	float temp_theta=0;
	int trans_c,trans_fl,trans_fr,trans_bl,trans_br=0; 
	int puck_in_hand, puck_in_line=0;
	
    set(DDRD,7);    // Set as Comm test Led output
	set(DDRD,6);    // Set as PAUSE Led output
    /*
	//ADC initialization
	clear(ADMUX,REFS1); //Set voltage reference for ADC as Vcc
	set(ADMUX,REFS0);   
	
	set(ADCSRA,ADPS2); //Prescale ADC to 250 Khz
	set(ADCSRA,ADPS1);
	clear(ADCSRA,ADPS0);
	 
	set(DIDR0,ADC1D); //Disabling Digital inputs for ADC pins
	set(DIDR0,ADC4D);
	set(DIDR0,ADC5D);
	set(DIDR0,ADC6D);
	set(DIDR0,ADC7D);
	*/	
    while  (m_wii_open()!=1){}
    
    //Timer Initialization
    set(DDRB, 6); // Set (Reg B. Bit 6) as timer output. PWM 1
    set(DDRB, 7); // Set (Reg B. Bit 7) as timer output. PWM 2
   
    set(TCCR1B, WGM13); // Set Timer 1 Mode 15 (UP to OCR1A, PWM mode)
    set(TCCR1B, WGM12);
    set(TCCR1A, WGM11);
    set(TCCR1A, WGM10);
   
    set(TCCR1A, COM1C1); // Clear at OCR1B. Set at rollover |Timer B.6
    clear(TCCR1A, COM1C0);

    set(TCCR1A, COM1B1); // Clear at OCR1C. Set at rollover |Timer B.7
    clear(TCCR1A, COM1B0);

    OCR1A=1600; //1Khz Motor
	OCR1B=0;
	OCR1C=0;
	
	clear(TCCR1B, CS12); // Initialize timer & Prescale /1 (Start Timer)
    clear(TCCR1B, CS11);
    set(TCCR1B, CS10);
   
    while(1)
	{

		while(!play) //PAUSE
		{
			m_green(OFF); 
			set(PORTD, 6); //Switch on RED LED
			OCR1B=0; //Stop Motor
			OCR1C=0; //Stop Motor
			clear(PORTB,6); //Stop Motor
			clear(PORTB,7); //Stop Motor
		}
		/*	
		//Trans_C
		clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
		
		clear(ADCSRB,MUX5); //Set MUX bit to F1
		clear(ADMUX,MUX2);
		clear(ADMUX,MUX1);
		set(ADMUX,MUX0);
		 
		set(ADCSRA,ADEN); //Enable the system
		set(ADCSRA,ADSC); //Start the conversion
	
		while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
		set(ADCSRA,ADIF);// Clear the flag
		 
		trans_c=ADC;
	
		//Trans_F_LEFT
		clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
		 
		clear(ADCSRB,MUX5); //set MUX bit to F4
		set(ADMUX,MUX2);
		clear(ADMUX,MUX1);
		clear(ADMUX,MUX0);
		 
		set(ADCSRA,ADEN); //Enable the system
		set(ADCSRA,ADSC); //Start the conversion
		 
		while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
		set(ADCSRA,ADIF);// Clear the flag
		 
		trans_fl=ADC;
		 
		//TRANS_F_RIGHT
		clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
		 
		clear(ADCSRB,MUX5); //Set MUX bit to F5
		set(ADMUX,MUX2);
		clear(ADMUX,MUX1);
		set(ADMUX,MUX0);
		 
		set(ADCSRA,ADEN); //Enable the system
		set(ADCSRA,ADSC); //Start the conversion
		 
		while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
		set(ADCSRA,ADIF);// Clear the flag
		 
		trans_fr=ADC;
	
		//TRANS_B_LEFT
		clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
		 
		clear(ADCSRB,MUX5); //Set MUX bit to F6
		set(ADMUX,MUX2);
		set(ADMUX,MUX1);
		clear(ADMUX,MUX0);
		 		 
		set(ADCSRA,ADEN); //Enable the system
		set(ADCSRA,ADSC); //Start the conversion
	
		while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
		set(ADCSRA,ADIF);// Clear the flag
		 
		trans_bl=ADC;
		 
		//TRANS_B_RIGHT
		clear(ADCSRA,ADEN); // Disable ADC system to change MUX bit
		 
		clear(ADCSRB,MUX5); //set MUX bit to F7
		set(ADMUX,MUX2);
		set(ADMUX,MUX1);
		set(ADMUX,MUX0);
		 
		set(ADCSRA,ADEN); //Enable the system
		set(ADCSRA,ADSC); //Start the conversion
	
		while(!check(ADCSRA,ADIF)){} //ADC conversion ongoing
		set(ADCSRA,ADIF);// Clear the flag
		 
		trans_br=ADC;
		*/	
	
		clear(PORTD,6); //Switch OFF RED LED
	
		cli();
		m_wii_read(star);
		sei();
		count=0;
		//Localization of bot w.r.t constellation
		//Reading no. of detectable stars
		for(k=0;k<=3;++k)
		{ 
			if((int)star[3*k]==1023 && (int)star[3*k+1]==1023)
				{count++;} //Count = No. of stars lost
		}
		if(count<=1) //Enter this only if <= 1 star has been lost. 
		{   
			m_red(OFF);    
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
						pmin=i*3; qmin=j*3; rmin=pmin+1; smin=qmin+1  ;
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
         
			m_usb_tx_string("  Theta_old: ");
			m_usb_tx_int(theta*57.6);
			//
			if(theta*57.6>=180)
			{	
				theta=theta-2*3.14;
			}
			/* if(theta*57.6<-180) // Why is this there?
			 { theta=2*3.14-theta;
			 }
			 */
	theta=-theta;
	/*
		//Puck detection
			//trans_c|trans_fl|trans_fr|trans_bl|trans_br| 
		while(!puck_in_hand)
		{
			if(trans_c>trans_fl && trans_c>trans_fr && trans_c>trans_bl && trans_c>trans_br) //Puck found! Go straight!
			{
				puck_in_line=1;
				temp1=MORE*OCR1A; //Straight!
				OCR1B=temp1;
				temp1=MORE*OCR1A;
				OCR1C=temp1;
			}
			else if( (trans_fr > trans_fl && trans_fr > trans_bl) || (trans_br >trans_fl && trans_br > trans_bl) ) //If right p_t> left p_t, Rotate Clockwise
			{
				temp1=LESS*OCR1A; //Clockwise
				OCR1B=temp1;
				temp1=MORE*OCR1A;
				OCR1C=temp1;
			}
			else //Rotate anti-clockwise
			{
				temp1=MORE*OCR1A;
				OCR1B=temp1;
				temp1=LESS*OCR1A;
				OCR1C=temp1;
				
			}
		
			}
	
		}*/
		
	
	
		//Goal detection (Activated once puck is detected <puck_in_hand>)
		to_angle_c=atan2(((goal_1+goal_2)/2-cY),(115-cX)); //Angle between the goal and current position
		to_angle_1=atan2((goal_1-cY),(115-cX)); //Angle between goal_1 (+y) and current position
		to_angle_2=atan2((goal_2-cY),(115-cX)); //Angle between goal_2 (-y) and current position
	
		
		if ( (to_angle_1*57.6>0 && to_angle_2*57.6>0) || (to_angle_1*57.6<0 && to_angle_2*57.6<0) ) //If both the angles are + or - (Out of scope of goal)
		{
			to_angle= (abs(to_angle_1*57.6) < abs(to_angle_2*57.6) ) ? to_angle_1 : to_angle_2; //to_angle = whichever is lesser 
		}
		else //Opposite sign (Within scope of goal)
		{
			to_angle=atan2(0,(115-cX)); //Go straight
		}
        //Difference 
		 m_usb_tx_string("  Theta-to_angle: ");
		 m_usb_tx_int((theta*57.6)-(to_angle*57.6));
		// temp_theta=(abs(theta*57.6)-abs(to_angle*57.6);
		// LESS2=( (MORE-LESS)/(10-temp_theta) )*(temp_theta-10) + MORE; 
		 
		if (theta*57.6<=to_angle*57.6+10 && theta*57.6>=to_angle*57.6-10) // Pointing to goal. Go straight.
		{
			temp1=MORE*OCR1A;
			OCR1B=temp1;
			temp1=MORE*OCR1A;
			OCR1C=temp1;
			m_green(ON);
			m_usb_tx_string("  ||STRAIGHT||");
		}
		else if( theta*57.6<(to_angle*57.6-10) ) //Rotate anti-clockwise
		{ 
			temp1=LESS*OCR1A;
			OCR1B=temp1;
			temp1=MORE*OCR1A;
			OCR1C=temp1;
			m_green(OFF);
			m_usb_tx_string("  ||ANTI-CLOCKWISE||");
		}
		   else if ( theta*57.6>(to_angle*57.6+10) ) //Rotate clockwise
		   {
				temp1=MORE*OCR1A;
				OCR1B=temp1;
				temp1=LESS*OCR1A;
				OCR1C=temp1;
				m_green(OFF);
			m_usb_tx_string("  ||CLOCKWISE||");
		   }
              

	set(PORTB,6);
	set(PORTB,7);
      
	}//end if (<= 1 star has been lost.)
   
    else //If more than 1 star has been lost:
    {   
        m_red(ON);
		OCR1B=0; //Stop the motor
		OCR1C=0;
        clear(PORTB,6); 
        clear(PORTB,7); 
        p=-1; q=-1; r=-1; s=-1;
        cxx=-1; cyy=-1;
        theta=0;
    }
    
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
    m_usb_tx_string("   Toangle_C: ");
    m_usb_tx_int(to_angle_c*57.6);
	m_usb_tx_string("   Toangle_1: ");
	m_usb_tx_int(to_angle_1*57.6);
	m_usb_tx_string("   Toangle_2: ");
	m_usb_tx_int(to_angle_2*57.6);
	m_usb_tx_string("   Toangle: ");
	m_usb_tx_int(to_angle*57.6);
    m_usb_tx_string("\n");
   m_wait(10);
   
    } ///while (1)
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
	if(buffer[0]==0xA0)	//COMM TEST
	{
		set(PORTD,7);
	}
	if(buffer[0]==0xA4) //PAUSE
	{
		set(PORTD,6); //Red LED ON 
		play=0;
	}
	sei();
}
