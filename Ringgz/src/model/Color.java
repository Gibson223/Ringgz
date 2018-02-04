package model;

/**
 * Represents a color in the Ringgz game. There four possible values: RED, YELLOW, GREEN & BLUE.
 * Module 2 programming project
 * 
 * @author Inigo Artolozaga & Gibson Vredeveld
 */
// RETURNS NEXT COLOR
/*
 * @ ensures this == Color.RED ==> \result == Color.YELLOW; ensures this == Color.YELLOW ==>
 * \result == Color.GREEN; ensures this == Color.GREEN ==> \result == Color.BLUE; ensures
 * this == Color.BLUE ==> \result == Color.RED;
 */
public enum Color {
    RED, YELLOW, GREEN, BLUE, INIT;

    public int colorWonFields;

    // from char to colors
    public static Color toColor(char a) {
        if (a == 'y') {
            return Color.YELLOW;
        } else if (a == 'b') {
            return Color.BLUE;
        } else if (a == 'g') {
            return Color.GREEN;
        } else if (a == 'r') {
            return Color.RED;
        } else {
            return null;
            // throw new Exception("InvalidCharException");
        }
    }

    public String toString() {
        if (this == Color.YELLOW) {
            return "y";
        } else if (this == Color.BLUE) {
            return "b";
        } else if (this == Color.GREEN) {
            return "g";
        } else if (this == Color.RED) {
            return "r";
        } else {
            return " ";
        }
    }

    // if this exception is given to client :redo
    // throw new RinggzException("InvalidColorException");
    public Color next() {
        if (this == Color.RED) {
            return YELLOW;
        } else if (this == YELLOW) {
            return GREEN;
        } else if (this == GREEN) {
            return BLUE;
        } else {
            return RED;
        }
    }
}