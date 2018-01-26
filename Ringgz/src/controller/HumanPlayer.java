package controller;
import java.util.Scanner;

import model.*;


/**
 * Class for maintaining a human player in Ringzz. Module 2 programming project
 */
public class HumanPlayer extends Player {
	
	private static final Scanner INPUT = new Scanner(System.in);

    // -- Constructors -----------------------------------------------

    /*@
       requires name != null;
       requires mark == Mark.XX || mark == Mark.OO;
       ensures this.getName() == name;
       ensures this.getMark() == mark;
    */
    /**
     * Creates a new human player object.
     * 
     */
    public HumanPlayer(String name) {
        super(name);
    }

    // -- Commands ---------------------------------------------------

    /*@
       requires board != null;
       ensures board.isField(\result) && board.isEmptyField(\result);

     */
    /**
     * Asks the user to input the field where to place the next ring, as well as what size of ring.
     * This is done using the standard input/output.
     * 
     * @param board
     *            the game board
     * @return the player's chosen field
     * @throws RinggzException 
     */
 
    @Override
	public void makeMove(Board board) {
    	String promptField = ("\n> " + getName() + " (" + getPrimaryColor().toString() + ")" + ", where will you place your ring? (field number)");
    	String promptRing = ("> " + getName() + " (" + getPrimaryColor().toString() + ")" + ", what kind of ring will you place? (1,2,3,4,5(BASE))");
    	String promptColor = ("> " + getName() + " (" + getPrimaryColor().toString() + ")" + ", what color do you want to play with? (r,g,b,y)");
		try {
			System.out.println(promptField);
	    	int choiceField = Integer.parseInt(INPUT.nextLine());
	    	if(board.firstMove) {
	    		if(board.middle9.stream().anyMatch(a -> a == choiceField) ) {
	    			board.specialbase(choiceField);
	    			board.firstMove = false;
	    			System.out.println("the first move has been placed");
	    			//ask how to show the view only once in the field if it is a firstmove
	    			return;
	    		} else { 
	    			System.out.println("this is the first move and the criteria for this are not met....");
	    			this.makeMove(board);
	    			return;
	    		}	    		
	    	}
	    	System.out.println(promptRing);
	    	int choiceRing = Integer.parseInt(INPUT.nextLine());
	    	System.out.println(promptColor);
	    	Color choiceColor = Color.toColor(INPUT.nextLine().charAt(0));
	    	Ring selectedRing = new Ring (choiceColor,Tier.toTier(choiceRing));
	    	
			if ( (board.isAllowed(choiceField, selectedRing) && 
					(choiceRing < 6) && (choiceRing > 0) && (choiceColor != null) 
					&& this.ringList.availableRings.contains(selectedRing))) {
				board.setRing(choiceField, selectedRing);
				this.ringList.availableRings.remove(selectedRing);
				System.out.println("\nthe ring has been added to the field....");
			} else {
				System.out.println("Invalid move, try another one.");
				this.makeMove(board);
			}
		} catch (RinggzException e) {
			this.makeMove(board);
		} catch (NullPointerException e) {
			System.out.println("invalid color, input your move again:\n");
			this.makeMove(board);
		} catch (NumberFormatException e) {
			System.out.println("invalid input, try again:\n");
			this.makeMove(board);
		}
    }

    /**
     * Writes a prompt to standard out and tries to read an int value from
     * standard in. This is repeated until an int value is entered.
     * 
     * @param prompt
     *            the question to prompt the user
     * @return the first int value which is entered by the user
     */
   

}
