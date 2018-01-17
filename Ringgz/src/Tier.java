public enum Tier{
	SMALL, MEDIUM, LARGE, LARGEST, BASE;
	public boolean occupied() {
		if(this == SMALL || this == MEDIUM || this == LARGE || this == BASE) {
			return true;
		} else {
			return false;
		}
	}
}
