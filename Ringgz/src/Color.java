

/**
 * Represents a color in the Ringgz game. There four possible values:
 * RED, YELLOW, GREEN & BLUE.
 * Module 2 programming project
 * 
 * @author Inigo Artolozaga & Gibson Vredeveld
 */
	
	public class Color{
	Color(String str) {
		this.str = str;
	}
	private final String str;
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
        if (this == Coloroptions.RED) {
            return YELLOW;
        } else if (this == YELLOW) {
            return GREEN;
        } else if (this == GREEN){
            return BLUE;
        } else {
            return RED;
        }
    }
    public enum Coloroptions {
	    RED , YELLOW , GREEN , BLUE , NULL;
		}
}
