package model;

public class ConstraintSet {
	
	
	private  final /*@ spec_public non_null @*/  ConstraintLista list;
	
	
	
	/* ensures isValidSet() == true ;
		also
		ensures (\forall Constraint constr; (constr != null) ==> belongs(constr) == false);
	*/
	public ConstraintSet(){
		list = new ConstraintLista();
	}
	
	
	/*@ ensures \result == list.hasItem(constr);
	 */
	public /*@ pure @*/ boolean belongs(/*@ non_null @*/ Constraint constr){
		return list.hasItem(constr);
	}
	
	/*@ requires (\exists int i; (i >= 0 && i < list.getSize() && list.getItem(i).isValid() == false));
	    ensures  \result == false;
 	*/
	public /*@ pure @*/ boolean isValidSet(){
		boolean res = true;
		
		/*@ loop_invariant list!= null ==> 
	    (\exists int j; (j >= 0 && j <= i 
		    && list.getItem(j).isValid() == false) ==>
		     res == false );
	   decreasing list.getSize()-i;
		  */
		for(int i = 0; i < list.getSize(); i++){
			res = true;
			if(!list.getItem(i).isValid()){
				res= false;
				break;
			}
		}//end of for loop
		
		
		return res;
	
	
	}
	
	

	/* ensures 
	(\forall  Constraint Constr2;
	@ belongs(Constr2 ) == \old((isEqual(Constr, Constr2)  ||  belongs(Constr2)))));
	@ also
	@ ensures 
	@( \old((isValidSet()  &&  Constr.isValid())) ==> 
	@ isValidSet() == true);
	@ also
	@*/
	public void add(Constraint Constr){
	
		
		
	}
	
	/* requires true;
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
