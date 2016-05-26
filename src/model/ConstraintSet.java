package model;

public class ConstraintSet {
	
	
	private  final /*@ spec_public non_null @*/  ConstraintLista list  ;
	
	/* public invariant list != null;
	 */ 
	
	/* ensures isValidSet() == true ;
		also
		ensures (\forall Constraint constr; (constr != null) ==> belongs(constr) == false);
	*/
	public ConstraintSet(){
		list = new ConstraintLista();
	}
	
	
	/*@ requires constr != null; 
	 ensures \result == list.hasItem(constr);
	 also
	 requires constr == null;
	 ensures \result == false;
	 */
	public /*@ pure @*/ boolean belongs(Constraint constr){
		if(constr != null)
			return list.hasItem(constr);
		else
			return false;
	}
	
	/*@ requires (\exists int i; (i >= 0 && i < list.getSize()); 
		    list.getItem(i).isValid() == false );
	  	ensures \result == false ;
	  	also
	    requires !(\exists int i; (i >= 0 && i < list.getSize()); 
		    list.getItem(i).isValid() == false );
	  	ensures \result == true ;
 	*/
	public /*@ pure @*/ boolean isValidSet(){
		boolean res = true;
		
		/*@ loop_invariant list!= null && i <= list.getSize() && i >=0 &&
	     ( (\exists int j; (j >= 0 && j < i); 
		    list.getItem(j).isValid() == false ) ==>
		     res == false ) &&
		     ( !(\exists int j; (j >= 0 && j < i); 
		    list.getItem(j).isValid() == false ) ==>
		     res == true );
	   decreasing list.getSize()-i;
		  */
		for(int i = 0; i < list.getSize(); i++){
			if(!list.getItem(i).isValid()){
				res= false;
				return res;
			}
		}//end of for loop
		return res;
	}
	
	

	/*
	 * @ also
	@ ensures 
	@( \old((isValidSet()  &&  Constr.isValid())) ==> 
	@ isValidSet() == true);

	
	 */
	
	
	/*@	requires constr.isValid();  
	 ensures (\forall  Constraint constr2; constr2 != null && constr.isEqual(constr2) 
	 			==> belongs(constr2) == true );
	 also
	 requires constr.isValid();
	 ensures (\forall  Constraint constr2; constr2 != null && !constr.isEqual(constr2) 
	 			==> belongs(constr2) == \old(belongs(constr2)));
	 also
	 requires isValidSet() && constr != null && constr.isValid();
	 ensures  constr.isValid() ==> isValidSet() == true;		
	*/
	public void add(/*@ non_null */ Constraint constr){
		if(constr != null && constr.isValid()){
			list.add(constr);
		}
		
		
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
