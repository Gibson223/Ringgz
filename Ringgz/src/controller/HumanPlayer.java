package controller;
import java.util.Scanner;

import model.*;


/**
 * Class for maintaining a human player in Ringzz. Module 2 programming project
 */
public class HumanPlayer extends Player {

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
    public HumanPlayer(String name, Color color, Color color2, RingList ringList) {
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
 
    public void makeMove(Board board) {
    	Scanner scanner = new Scanner(System.in);
    	String promptField = ("\n> " + getName() + " (" + getPrimaryColor().toString() + ")" + ", where will you place your ring?");
    	String promptRing = ("> " + getName() + " (" + getPrimaryColor().toString() + ")" + ", what kind of ring will you place (1,2,3,4,5(BASE))?");
    	String promptColor = ("> " + getName() + " (" + getPrimaryColor().toString() + ")" + ", what color do you want to play with?");
    	System.out.println(promptField);
    	int choiceField = Integer.parseInt(scanner.nextLine());
    	System.out.println(promptRing);
    	int choiceRing = Integer.parseInt(scanner.nextLine());
    	System.out.println(promptColor);
    	Color choiceColor = Color.toColor(scanner.nextLine());
    	// would be nice if catch the exception and then reinvoke makeMove. That way we solve wrong input immediately
		try {
			if (board.isAllowed(choiceField, new Ring (choiceColor,Tier.toTier(choiceRing)))) {
				board.setRing(choiceField, new Ring (choiceColor,Tier.toTier(choiceRing)));
				this.ringList.availableRings.remove(new Ring (choiceColor,Tier.toTier(choiceRing)));
				System.out.println("the ring has been added to the field....");
			} else {
				System.out.println("Invalid move, try another one.");
				this.makeMove(board);
			}
		} catch (RinggzException e) {
			this.makeMove(board);
		}
    	scanner.close();
    }

    /**
     * Writes a prompt to standard out and tries to read an int value from
     * standard in. This is repeated until an int value is entered.
     * 
     * @param prompt
     *            the question to prompt the user
     * @return the first int value which is entered by the user
     */
    private int readInt(String prompt) {
        int value = 0;
        boolean intRead = false;
        @SuppressWarnings("resource")
        Scanner line = new Scanner(System.in);
        do {
            System.out.print(prompt);
            try (Scanner scannerLine = new Scanner(line.nextLine());) {
                if (scannerLine.hasNextInt()) {
                    intRead = true;
                    value = scannerLine.nextInt();
                }
            }
        } while (!intRead);
        return value;
    }

}
