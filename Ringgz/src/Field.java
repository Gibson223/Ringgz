import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

public class Field {
	private static int count = 1;
	public int FieldNumber;
	
	Field(){
		FieldNumber = count;
		count++;
		fieldState.add(new Ring());
		fieldState.add(new Ring());
		fieldState.add(new Ring());
		fieldState.add(new Ring());
	}
	
	//small to large; 
	//1 = small 
	//4 = large;
	private List<Ring> fieldState = new ArrayList<>();
	public List<Ring> getFieldState() {
		return fieldState ;
	}
	
	//ROW-COLUMN ADAPTATION FOR getFieldState ABOVE
	
	//RETURNS WHETHER OR NOT A FIELD HAS A CERTAIN COLOR RING
	public boolean HasColor(Color color) {
		for (Ring ring : fieldState) {
			if (ring.getColor() == color) {
				return true;
			}
		}
		return false;
	}
	public boolean HasBase() {
		for (Ring ring: fieldState)
			if (ring.getTier() == Tier.BASE) {
				return true;
			}
		return false;
	}
	public boolean isFull() {
		if (this.HasBase()) {
			return true;
		}
		for (Ring ring: fieldState) {
			if (!ring.getTier().occupied()) {
				return false;
			}
		}
		return true;
	}
	public boolean isAllowed(Ring r) {
		if (this.HasBase()) {
			return false;
		}
		for (Ring ring : fieldState){
			if (ring.getTier() == r.getTier()) {
				System.out.println("Tier already present..");
				return false;
			}
		}
		return true;
	}
	public void setRing(Ring ring) {
		if(this.isAllowed(ring)) {
			fieldState.remove(0);
			fieldState.add(ring);
		}
	}
	public static void main(String[] args) {
		Field a = new Field();
		Ring ring = new Ring(Color.BLUE, Tier.BASE);
		Ring ring2 = new Ring(Color.GREEN, Tier.BASE);
		System.out.println(ring);
		System.out.println(a.FieldNumber);
		System.out.println(a.fieldState);
		a.setRing(ring);
		System.out.println(a.fieldState);
		a.setRing(ring);
		a.setRing(ring2);
		System.out.println(a.fieldState);
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