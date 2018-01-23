package model;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

public class Field {
	private static int count = 1;
	public int FieldNumber;
	
	public Field(){
		FieldNumber = count;
		count++;
		this.initfieldState();
	}
	public void initfieldState() {
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
	// for proximity check
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
	public Color isWinner() {
		Map<Color, Integer> map = new HashMap<>();
		for (Ring f : fieldState){
		    if (map.containsKey(f.getColor())) { 
		        map.put(f.getColor(),map.get(f.getColor())+1);
		    } else {
		        map.put(f.getColor(), new Integer(1));
		    }
		}
		map.remove(null);
		System.out.println(map);
		Integer highest = java.util.Collections.max(map.values());
		if (java.util.Collections.frequency(map.values(), highest) == 1) {
		for (Map.Entry<Color, Integer> c: map.entrySet()) {
				if (c.getValue() == highest) {
					return c.getKey();
				}
			}
		}
		return null;
	}
	public static void main(String[] args) {
		Field a = new Field();
		Ring ring = new Ring(Color.BLUE, Tier.MEDIUM);
		Ring ring2 = new Ring(Color.GREEN, Tier.SMALL);
		Ring ring3 = new Ring(Color.GREEN, Tier.LARGE);
		System.out.println(ring);
		System.out.println(a.FieldNumber);
		System.out.println(a.fieldState);
		a.setRing(ring);
		System.out.println(a.fieldState);
		a.setRing(ring);
		a.setRing(ring2);
		a.setRing(ring3);
		System.out.println(a.fieldState);
		System.out.println(a.isWinner());
	}
	public void clear() {
		this.initfieldState();
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