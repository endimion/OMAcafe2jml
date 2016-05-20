package model;

public class ConstraintSet {
	
	
	
	/*@ initially
	@ (\forall  Constraint Constr;
	  @ belongs(Constr) == false &&
	  @ isValidSet() == true);
	 @*/
	
	private /*@ spec_public non_null @*/ ConstraintLista list;
	
	public ConstraintSet(){
		list = new ConstraintLista();
	}
	
	
	public /*@ pure @*/ boolean belongs(Constraint Constr){
		//return list.;
		return false;
	}
	public /*@ pure @*/ boolean isValidSet(){return false;}
	
	
	/*@ ensures 
	(\forall  Constraint Constr2;
	@ belongs(Constr2 ) == \old((isEqual(Constr, Constr2)  ||  belongs(Constr2)))));
	@ also
	@ ensures 
	@( \old((isValidSet()  &&  isValid(Constr))) ==> 
	@ isValidSet() == true);
	@ also
	@*/
	public void add(Constraint Constr){}
	
	/*@ requires true;
	@ ensures 
	(\forall  Constraint Constr2;
	@( \old(isEqual(Constr, Constr2)) ==> 
	@ belongs(Constr2 ) == false));
	@ also
	@ requires true;
	@ ensures 
	@  (\forall  Constraint Constr2;
	@( \old(not(isEqual(Constr, Constr2))) ==> 
	@ belongs(Constr2 ) == \old(belongs(Constr2))));
	@ also
	@ requires true;
	@ ensures 
	@(
	@ isValidSet() == \old(isValidSet()));
	@ also
	@*/
	public void rem(Constraint Constr){}
	
		
	
	
	
}
