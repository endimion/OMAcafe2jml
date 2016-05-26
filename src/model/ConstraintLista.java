package model;

public class ConstraintLista {

	private /*@ spec_public non_null@*/  Constraint[] items ;
	/*@  public invariant items != null  && 0 <= items.length 
	            && (\typeof(items) == \type(Constraint[]) ) 
	 			&&	\elemtype(\type(Constraint[])) == \type(Constraint);
	 */
	
	public final /*@ non_null @*/ Constraint err ;
	
	/* ensures items!=null && items.length == 0 &&
	  (\forall Constraint c;  c!=null ==> hasItem(c) == false) && err!=null;*/
	public ConstraintLista(){
		items = new Constraint[0];
		err = new Constraint();
	}
	
	/*@ requires items.length > 0 && id >= 0 && id < items.length && items[id] != null;
 	 @ ensures \result == items[id] ;
 	 @ also
 	 @ requires !(items.length > 0 && id >= 0 && id < items.length && items[id] != null);
 	 @ ensures \result == err ;
 	 */
	public /*@ pure non_null @*/ Constraint getItem(int id){
		
		if(items.length > 0 && id >= 0 && id < items.length && items[id] != null){
			return items[id];
		}else{
			return err;
		}
	}//getItem
	
	
	/*@ ensures \result == items.length;
	    @ also
	    @ ensures \result >= 0; 
	 */
	public /*@ pure @*/ int getSize(){return items.length;}
	
	
	
	/*@ requires items != null  && items.length  >=0 && size > items.length && size > 0;
		@ ensures items != null ;
		@ assignable items;
		@ also
		@ requires items != null  && items.length  >=0 && size > items.length && size > 0;
		@ ensures items.length == size;
		@ assignable items;
		@ also
		@ requires items != null  && items.length  >=0 && size > items.length && size > 0;
		@ ensures (\forall int j; j >=0 && j < \old(items.length); items[j] == \old(items[j]) );
		@ assignable items;
		@ also
		@ requires !(items != null  && items.length  >=0 && size > items.length && size > 0);
		@ assignable \nothing;
	 */
	public  void resizeArray( int size){

		if(items != null  && items.length  >=0 && size > items.length && size > 0){
			Constraint[] temp = new Constraint[size];
			/*@ loop_invariant items!= null && temp != null && (items.length < temp.length) ==> 
		    (\forall int j; (j >= 0 && j < i  )
		     ==> ( (j < items.length) ==> temp[j] == items[j] )
		      && (!(j < items.length) ==>  temp[j] == null) ) ;
		   decreasing temp.length-i;
			  */
			for(int i = 0; i < temp.length; i++){
				if(i < items.length && i >=0 ) temp[i] = items[i];
				 else{ 
					 if(i >=0)  temp[i] = null;
				 }
			 }//end of for loop
			items =temp;
		}
	}//end of reseizeArray

	
	/*@ requires items != null  && items.length  >0 && it != null 
	  	&& (\exists int i; (i >= 0 && i < items.length && getItem(i).isEqual(it)));
   	ensures  \result == true;
   	also
   	requires items != null  && items.length  >0 && it != null 
   							&& !(\exists int i; (i >= 0 && i < items.length && 
    						    getItem(i).isEqual(it)));
    ensures \result == false;
    also
    requires !(items != null  && items.length  >0 && it != null);
    ensures  \result == false; 						    
    */
	public /*@ pure @*/ boolean hasItem(Constraint it){
		
		
		boolean found = false;
		if(items != null && items.length >0 && it != null ){
			/*@ loop_invariant 
			 items!= null && it != null && i <= items.length && i >=0 && items.length >= 0 &&
		    	( (\exists int j; (j >= 0 && j < i && j < items.length   
		    				  && getItem(j)!=null && getItem(j).isEqual(it))) ==>
		     found == true ) &&
		     ( !(\exists int j; (j >= 0 && j < i && j < items.length   
		    				  && getItem(j)!=null && getItem(j).isEqual(it))) ==>
		     found == false );
		     decreasing items.length-i;
			*/
			for(int i = 0; i < items.length; i++){
				if(i < items.length && i >=0){
					//if(getItem(i) != null && getItem(i).isEqual(it)){
						if( getItem(i)!=null && getItem(i).isEqual(it)){
							found = true;
							//return res;
						}
					//}
				}//end of if
				//res = false;
			 }//end of for loop
			
		}
		return found;
	}	

	/*@ requires it != null &&  pos >= 0 && pos < items.length;
			ensures getItem(pos) == it;
			assignable items[pos];
			also
			requires it != null &&  pos >= 0 && pos < items.length;
			ensures getSize() == \old(getSize());
			assignable items[pos];
			also  
			requires !(it != null &&  pos >= 0 && pos < items.length);
			assignable \nothing;
	 */
	public void assign(/*@ non_null @*/ Constraint it, int pos){
		if(it != null && pos >=0 && pos < items.length){
			items[pos] = it;
		}
	}
	
	

	/*@ requires   pos >= 0 && pos >= getSize() && getSize() >0 ;
	 		 ensures items != null && getSize() == pos+1;
	 		 also
	 		 requires   pos >= 0 && pos >= getSize() && getSize() >0 ;
	 		 ensures getItem(pos) == it;
	 		 also
	 		 requires   pos >= 0 && pos < getSize() && getSize() >0 ;
	 		 ensures getItem(pos) == it;
	 		 also
	 		 requires   pos >= 0 && pos < getSize() && getSize() >0 ;
	 		 ensures \old(getSize()) == getSize();
	 		 assignable items[pos];
	 		 also
	 		 requires !(pos >=0 && getSize() > 0);
	 		 assignable \nothing; 
	 */
	public void setItem(int pos, /*@ non_null @*/ Constraint it){
		if( items != null  && items.length  >0 && pos >= items.length && pos > 0){
			resizeArray(pos+1);
			if(it != null && pos >= 0 && pos < items.length){ 
				assign(it,pos);
			}
		}
		
		if( items != null  && items.length  >0 && pos < items.length && pos >= 0){
			if(it != null && pos >= 0 && pos < items.length){ 
				assign(it,pos);
			}
		}
	}//end of setItem
	
	
	
	
	
	
	/*@ ensures getSize() > 0;
	    @ also
	    @ requires getSize() > 0;
	  	@ ensures getItem(getSize()-1) == obj;
	  	@ also 
	  	@ requires getSize() == 0;
	  	@ ensures getItem(getSize()-1) == obj;
	  	@ also
	  	@ ensures  hasItem(obj) == true;
	  	@ also
	  	@ ensures  (\forall Constraint constr; (constr != null && !obj.isEqual(constr)) ==> hasItem(constr) == \old(hasItem(constr)) );
	 */
	public void add(/*@ non_null @*/ Constraint obj){
		if(getSize() >0){
			setItem(getSize(),obj) ;
		}else{
			if(getSize() == 0){
				resizeArray(1);
				items[0] = obj;
			}
		}
	}
	
	
}//end of lista
