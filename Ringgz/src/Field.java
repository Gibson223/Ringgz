import java.util.List;

public class Field {
	private static int count = 1;
	public int FieldNumber;
	
	Field(){
		FieldNumber = count;
		count++;
		FieldState[0] = Tier1;
		
		
		
	}
	
	//small to large; 
	//1 = small 
	//4 = large;
	private Ring Tier1 ;
	private Ring Tier2 ;
	private Ring Tier3 ;
	private Ring Tier4 ;
	List<String> FieldsState = Arrays.asList(Tier1,Tier2,Tier3,Tier4);
	
	public List<> getFieldState(int field) {
		return FieldState;
	}
	
	
	//ROW-COLUMN ADAPTATION FOR getFieldState ABOVE
	
	//RETURNS WHETHER OR NOT A FIELD HAS A CERTAIN COLOR RING
	public boolean FieldHas(int field, Color color) {
		return (field.FieldTier[0] == color || field.FieldTier[1] == color || field.FieldTier[2] == color || field.FieldTier[3] == color);
	}
}
	//getfield should have array
	//WE NEED AN ARRAY LIST FOR EACH FIELD WITH 4 SLOTS (FieldTier) 
	//EACH SLOT REPRESENTS ONE SIZE RING
	//WE NEED TO HAVE THE POWER TO MODIFY A CERTAIN SLOT OF THE ARRAY WHEN A PLAYER PLACES A RING
	//GETTERS AND SETTERS (getSlot(field,slot) and setSlot(field,slot))
	//THE SETTER CHECKS FIRST IF THE SLOT IS AVAILABLE WITH THE GETTER
	//IF THE PLAYER PLACES A BASE, THE FieldState CHANGES AUTOMATICALLY TO THE PLAYER'S COLOR
	//WE NEED A CHECKER TO CHECK IF A FIELD IS FULL INSIDE THE SETTER
	//WE NEED A METHOD THAT IS CALLED WHEN A FIELD IS FULL THAT DETERMINES THE WINNER OF THAT FIELD
	//WE NEED A METHOD CALLED FieldHas(field,color) THAT SAYS IF A RING OF color IS IN THAT field