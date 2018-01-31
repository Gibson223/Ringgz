package model;

public enum Tier {
	SMALLEST, SMALL, MEDIUM, LARGE, BASE, INIT;
	public boolean occupied() {
		if (this == SMALLEST || this == SMALL || this == MEDIUM || this == LARGE || this == BASE) {
			return true;
		} else {
			return false;
		}
	}

	public static Tier toTier(int i) {
		if (i == 1) {
			return Tier.BASE;
		} else if (i == 2) {
			return Tier.SMALLEST;
		} else if (i == 3) {
			return Tier.SMALL;
		} else if (i == 4) {
			return Tier.MEDIUM;
		} else if (i == 5) {
			return Tier.LARGE;
		} else {
			return null;
		}
	}
}
