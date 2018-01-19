

/**
 * Represents a color in the Ringgz game. There four possible values:
 * RED, YELLOW, GREEN & BLUE.
 * Module 2 programming project
 * 
 * @author Inigo Artolozaga & Gibson Vredeveld
 */
	//RETURNS NEXT COLOR
    /*@
       ensures this == Color.R ==> \result == Color.Y;
       ensures this == Color.Y ==> \result == Color.G;
       ensures this == Color.G ==> \result == Color.B;
       ensures this == Color.B ==> \result == Color.R;
     */
public enum Color {
	    RED , YELLOW , GREEN , BLUE;
	//from char to color
	public Color toColor(char a) {
		if (a == 'y') {
			return Color.YELLOW;
		}else if (a == 'b') {
			return Color.BLUE;
		} else if (a == 'g') {
			return Color.GREEN;
		} else if (a == 'r') {
			return Color.RED;
		} else {
		return null;
		}
	}
	public Color next() {
        if (this == Color.RED) {
            return YELLOW;
        } else if (this == YELLOW) {
            return GREEN;
        } else if (this == GREEN){
            return BLUE;
        } else {
            return RED;
        }
	}
}