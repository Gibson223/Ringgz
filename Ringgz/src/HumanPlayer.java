import java.util.Scanner;


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
    public HumanPlayer(String name, Color color) {
        super(name, color);
    }

    // -- Commands ---------------------------------------------------

    /*@
       requires board != null;
       ensures board.isField(\result) && board.isEmptyField(\result);

     */
    /**
     * Asks the user to input the field where to place the next mark. This is
     * done using the standard input/output. \
     * 
     * @param board
     *            the game board
     * @return the player's chosen field
     */
    public int determineMove(Board board) {
        String promptField = "> " + getName() + " (" + getColor().toString() + ")" + ", where will you place your ring? ";
        int choiceField = readInt(promptField);
        boolean validField = board.isField(choiceField) && board.isAvailableField(choiceField);
        while (!validField) {
            System.out.println("ERROR: field " + choiceField + " is no valid choice.");
            choiceField = readInt(promptField);
            validField = board.isField(choiceField) && board.isAvailableField(choiceField);
        }
        String promptRing = "> " + getName() + " (" + getColor().toString() + ")" + ", what kind of ring will you place?";
        int choiceRing = readInt(promptRing);
        boolean validRing = board.isField(choiceRing) && board.isAvailableField(choiceRing);
        while (!validRing) {
            System.out.println("ERROR: Ring " + choiceRing + " is no valid choice.");
            choiceRing = readInt(promptRing);
            validRing = board.isField(choiceRing) && board.isAvailableField(choiceRing);
        }
        return choiceRing;
        return choiceField;
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
