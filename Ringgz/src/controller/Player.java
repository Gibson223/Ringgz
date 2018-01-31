package controller;
import model.*;

import java.util.*;

public abstract class Player {
    // -- Instance variables -----------------------------------------

    public  final String name;
    private Color  primary;
    private Color secondary;
    private Board board;
    
    public Player(String name) {
    	this.name = name;
    	this.potentialFields = new LinkedList<Field>();
    	this.board = new Board();
    }
	public void setPrimary(Color primary) {
		this.primary = primary;
	}

	public void setSecondary(Color secondary) {
		this.secondary = secondary;
	}

	public void setRingList(RingList ringList) {
		this.ringList = ringList;
	}


	public RingList ringList;
	public final List<Field> potentialFields;
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
	
//    public Player(String name, Color color, RingList ringList)
//	{ //TODO: make it possible to assign more than one color to a single player
//        this.name = name;
//        this.primary = color;
//    }
//    public Player(String name, Color primary, Color secondary, 
//		RingList ringList) { //TODO: make it possible to assign more than one color to a single player
//        this.name = name;
//        this.primary = primary;
//        this.secondary = secondary;
//        this.ringList = ringList;

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
    //returns false if no move is available
    public boolean playerCheck() throws RinggzException {
    	boolean validringmove = false;
    	if (this.board.firstMove) {
    		return true;
    	}
    	for (Ring ring: this.ringList.availableRings) {
    		for (Field field: this.board.fields) {
    			if (this.board.isAllowed(field.FieldNumber, ring) && 
    					(this.board.proximityCheck(field.FieldNumber, this.getPrimaryColor()) || 
    							this.board.FieldHasColor(field.FieldNumber, 
    									this.getPrimaryColor()))) {
    				validringmove = true;
    				break;
    			}
    		}
    	}
    	if (!this.ringList.availableRings.isEmpty() && validringmove) {
    		return true;
    	} else {
    		return false;
    	}
    }
    public void makeMove() throws RinggzException {
    	this.makeMove(this.board);
    }
    public abstract void makeMove(Board board) throws RinggzException;
}
