package controller;
import model.Board;
import model.Color;
import java.util.*;

public abstract class Player {
    // -- Instance variables -----------------------------------------

    public String name;
    private Color primary;
    private Color secondary;
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
    public Player(String name, Color color) { //TODO: make it possible to assign more than one color to a single player
        this.name = name;
        this.primary = color;
    }
    public Player(String name, Color primary, Color secondary) { //TODO: make it possible to assign more than one color to a single player
        this.name = name;
        this.primary = primary;
        this.secondary = secondary;
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

    /*@
       requires board != null & !board.isFull();
       ensures board.isField(\result) & board.isEmptyField(\result);
     */
    /**
     * Determines the field for the next move.
     * 
     * @param board
     *            the current game board
     * @return the player's choice
     */
    public abstract List<Integer> determineMove(Board board);

    // -- Commands ---------------------------------------------------

    /*@
       requires board != null & !board.isFull();
     */
    /**
     * Makes a move on the board. <br>
     * 
     * @param board
     *            the current board
     */
    public void makeMove(Board board) {
        int choice = determineMove(board);
        board.setField(choice, getColor(), Ring.RingType.getRing()//TODO);
    }

}
