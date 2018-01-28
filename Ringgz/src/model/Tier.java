package model;
public enum Tier {
	SMALL, MEDIUM, LARGE, LARGEST, BASE, INIT;
	public boolean occupied() {
		if (this == SMALL || this == MEDIUM || this == LARGE || this == LARGEST || this == BASE) {
			return true;
		} else {
			return false;
		}
	}
	public static Tier toTier(int i) {
		if (i == 1) {
			return Tier.SMALL;
		} else if (i == 2) {
			return Tier.MEDIUM;
		} else if (i == 3) {
			return Tier.LARGE;
		} else if (i == 4) {
			return Tier.LARGEST;
		} else if (i == 5) {
			return Tier.BASE;
		} else {
			return null;
		}		
	}
}
