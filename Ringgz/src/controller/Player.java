package controller;
import model.*;

import java.util.*;

public abstract class Player {
    // -- Instance variables -----------------------------------------

    public String name;
    private Color primary;
    private Color secondary;
	public RingList ringList;
	public List<Field> potentialFields = new LinkedList<>();
    // -- Constructors -----------------------------------------------

    /*@
       requires name != null;
       ensures this.getName() == name;
       ensures this.getColor() == color;
     */
    /**
     * Creates a new Player object.
     * 
     */
    public Player(String name, Color color, RingList ringList) { //TODO: make it possible to assign more than one color to a single player
        this.name = name;
        this.primary = color;
    }
    public Player(String name, Color primary, Color secondary, RingList ringList) { //TODO: make it possible to assign more than one color to a single player
        this.name = name;
        this.primary = primary;
        this.secondary = secondary;
        this.ringList = ringList;
    }

    // -- Queries ----------------------------------------------------

    
     //Returns the name of the player.	     
    /*@ pure */
    public String getName() {
        return name;
    }

     //Returns the primary color of the player.	   
    /*@ pure */
    public Color getPrimaryColor() {
        return primary;
    }
    
  //Returns the secondary color of the player.	   
    /*@ pure */
    public Color getSecondaryColor() {
        return secondary;
    }


    // -- Commands ---------------------------------------------------

    /*@
       requires board != null & !board.isFull();
     */
    /**
     * Makes a move on the board. <br>
     * 
     * @param board
     *            the current board
     * @throws RinggzException 
     */
    public abstract void makeMove(Board board) throws RinggzException;
}
