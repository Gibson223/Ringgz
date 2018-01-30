package model;

public class Ring {
	private Color color;
	private Tier tier;

	public Ring(Color c, Tier t) {
		color = c;
		tier = t;
	}
	
	
	//@requires color != null;
	//@requires tier != null;
	//@ensures color == this.getColor;
	//@ensures tier == this.getTier();
	public Ring() {
		color = Color.INIT;
		tier = Tier.INIT;
	}

	//@requires tier != null;
	//@ensures tier == this.getTier;
	public void setTier(Tier tier) {
		this.tier = tier;
	}

	//@ensures 
	public Tier getTier() {
		return tier;
	}

	public Color getColor() {
		return color;
	}

	public void setColor(Color color) {
		this.color = color;
	}

	// CHECKS IF THE CHOSEN RING IS A VALID CHOICE
	public static boolean isRing(Tier choice) {
		for (Tier aType : Tier.values()) {
			if (aType == choice) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean equals(Object ring) {
		if (ring instanceof Ring && ((Ring) ring).getColor() == this.getColor()
				&& ((Ring) ring).getTier() == this.getTier()) {
			return true;
		}
		return false;

	}

	// returns the color of the ring in a String
	@Override
	public String toString() {
		return this.getColor().toString();
	}
}
