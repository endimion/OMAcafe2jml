package model;

public class Constraint {
	
	/*@ initially
	  @ isValid() == false &&
	  @ isInit() == false &&
	  @ isDate() == false &&
	  @ isCount() == false &&
	  @ getCount() == -1 &&
	  @ getDate() == -1;
	 @*/
	
		private /*@ spec_public @*/ boolean isValid;
		private /*@ spec_public @*/ boolean isInit;
		private /*@ spec_public @*/ boolean isDate;
		private /*@ spec_public @*/ boolean isCount;
		private /*@spec_public @*/ int the_date;
		private /*@spec_public @*/ int the_count;
		
	public Constraint(){
		this.isValid = false;
		this.isInit = false;
		this.isDate = false;
		this.isCount = false;
		this.the_date=-1;
		this.the_count = -1;
	}
	
	/* @ ensures \result == (this.isCount() == c.isCount() && this.isDate() == c.isDate()
	&& this.isInit() == c.isInit() && this.isValid() == c.isValid() && this.getCount() == c.getCount()
	&& this.getDate() == c.getDate()); 
	*/
	public /*@ pure @*/ boolean isEqual(/*@ non_null@*/ Constraint c){
		return this.isCount() == c.isCount() && this.isDate() == c.isDate()
				&& this.isInit() == c.isInit() && this.isValid() == c.isValid() && this.getCount() == c.getCount()
				&& this.getDate() == c.getDate();
	}
	
	/*@ ensures \result == this.isValid;
	public /*@ pure @*/ boolean isValid(){
		return this.isValid;
	}
	//@ ensures \result == this.isInit;
	public /*@ pure @*/ boolean isInit(){return this.isInit;}
	
	//@ ensures \result == this.isDate;
	public /*@ pure @*/ boolean isDate(){return this.isDate;}
	
	//@ ensures \result == this.isCount;
	public /*@ pure @*/ boolean isCount(){return this.isCount;}
	
	//@ ensures \result == this.the_count;
	public /*@ pure @*/ int getCount(){return this.the_count;}
	//@ ensures \result == this.the_date;
	public /*@ pure @*/ int getDate(){return this.the_date;}
	
	/*@ ensures
	@ \result == (isInit()  ==  false);
	@*/
	public /*@ pure @*/ boolean cmakeDateTime(){return this.isInit() == false;}
	
	/*@ ensures
	@ \result == (isInit()  ==  false);
	@*/
	public /*@ pure @*/ boolean cmakeCount(){return this.isInit() == false;}
	
	
	/*@ requires cmakeDateTime();
	@ ensures 
	@ isValid() == true;
	@ also
	@ requires cmakeDateTime();
	@ ensures 
	@ isInit() == true;
	@ also
	@ requires cmakeDateTime();
	@ ensures  isDate() == true;
	@ also
	@ requires cmakeDateTime();
	@ ensures isCount() == false;
	@ also
	@ requires cmakeDateTime();
	@ ensures getDate() == aDate;
	@ also
	@ requires cmakeDateTime();
	@ ensures getCount() == \old(getCount());
	@ also
	@ requires !cmakeDateTime();
	@ assignable \nothing;
	@*/
	public void makeDateTime(int aDate){
		if(cmakeDateTime()){
			this.isDate = true;
			this.the_date = aDate;
			this.isCount = false;
			this.isValid = true;
			this.isInit = true;
		}
	}
	
	/*@ requires cmakeCount();
	@ ensures 
	@ isValid() == true;
	@ also
	@ requires cmakeCount();
	@ ensures 
	@ isInit() == true;
	@ also
	@ requires cmakeCount();
	@ ensures 
	@ isDate() == false;
	@ also
	@ requires cmakeCount();
	@ ensures 
	@ isCount() == true;
	@ also
	@ requires cmakeCount();
	@ ensures 
	@ getDate() == \old(getDate());
	@ also
	@ requires cmakeCount();
	@ ensures 
	@ getCount() == NumberOfCount;
	@ also
	@ requires  !cmakeCount();
	@  assignable \nothing;
	@*/
	public void makeCount(int NumberOfCount){
		if(cmakeCount()){
			this.the_count= NumberOfCount;
			this.isCount = true;
			this.isInit = true;
			this.isValid = true;
			this.isDate = false;
		}
	}


}