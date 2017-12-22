

/**
 * Represents a color in the Ringgz game. There four possible values:
 * RED, YELLOW, GREEN & BLUE.
 * Module 2 programming project
 * 
 * @author Inigo Artolozaga & Gibson Vredeveld
 */
public enum Color {
    
    RED ("R"), YELLOW ("Y"), GREEN ("G"), BLUE ("B"), NULL ("-");

	private final String str;
	
	Color(String str) {
		this.str = str;
	}
	
	@Override
	public String toString() {
		return str;
	}
	
	//RETURNS NEXT COLOR
    /*@
       ensures this == Color.R ==> \result == Color.Y;
       ensures this == Color.Y ==> \result == Color.G;
       ensures this == Color.G ==> \result == Color.B;
       ensures this == Color.B ==> \result == Color.R;
     */
    public Color next() {
        if (this == RED) {
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
