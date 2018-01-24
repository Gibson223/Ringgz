package model;

public class Ring {
	private Color color;
	private Tier tier;
	Ring(Color c, Tier t){
		color = c;
		tier = t;
	}
	public Ring() {
	}
	public void setTier(Tier tier) {
		this.tier = tier;
	}
	public Tier getTier() {
		return tier;
	}
	public Color getColor() {
		return color;
	}
	public void setColor(Color color) {
		this.color = color;
	}
	//CHECKS IF THE CHOSEN RING IS A VALID CHOICE IN THE ENUM ABOVE
	//@ensures //TODO
	public static boolean isRing(Tier choice) {
	   for(Tier aType : Tier.values()) {
	      if(aType == choice) {
	         return true;
	      }
	   }
	   return false;
	}
	@Override
	 public boolean equals(Object ring){
		if (ring instanceof Ring && ((Ring) ring).getColor() == this.getColor() && ((Ring) ring).getTier() == this.getTier() ) {
			
		}
		return false;
		
	}
	//returns the color of the ring
	@Override
	public String toString() {
		return this.getColor().toString();
	}
}
