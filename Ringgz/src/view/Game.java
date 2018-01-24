package view;


import java.util.Scanner;

import controller.Player;
import model.Board;

/**
 * Class for maintaining the Ringgz game.
 * @author Inigo Artolozaga and Gibson Vredeveld
 */
public class Game {
    public static final int NUMBER_PLAYERS = 4; //TODO make this modifiable;

    /*@ private invariant board != null; */
    /**
     * The board.
     */
    private Board board;

    /*@  private invariant players.length == NUMBER_PLAYERS;
        private invariant (\forall int i; 0 <= i && i < NUMBER_PLAYERS; 
       	                           players[i] != null); 
     */
    /**
     * The players of the game.
     */
    private Player[] players;

    /*@ private invariant 0 <= current  && current < NUMBER_PLAYERS; */
    /**
     * Index of the current player.
     */
    private int current;

    // -- Constructors -----------------------------------------------

    /*@ requires s0 != null;
        requires s1 != null;
     */
    /**
     * Creates a new Game object.
     * @param s0 the first player
     * @param s1 the second player
     */
    public Game(Player s0, Player s1, Player s2, Player s3) { // TODO make this not hardcoded for 4 players;
        board = new Board();
        players = new Player[NUMBER_PLAYERS];
        players[0] = s0;
        players[1] = s1;
        players[2] = s2;
        players[3] = s3;
        current = 0;
    }

    // -- Commands ---------------------------------------------------

    /**
     * Starts the Tic Tac Toe game. <br>
     * Asks after each ended game if the user want to continue. Continues until
     * the user does not want to play anymore.
     */
    public void start() {
        boolean again = true;
        while (again) {
            play();
            again = readBoolean("\n> Play another time? (y/n)?", "y", "n");
            reset();
        }
    }

    /**
     * Prints a question which can be answered by yes (true) or no (false).
     * After prompting the question on standard out, this method reads a String
     * from standard in and compares it to the parameters for yes and no. If the
     * user inputs a different value, the prompt is repeated and te method reads
     * input again.
     * 
     * @param prompt the question to print
     * @param yes
     *            the String corresponding to a yes answer
     * @param no
     *            the String corresponding to a no answer
     * @return true is the yes answer is typed, false if the no answer is typed
     */
    private boolean readBoolean(String prompt, String yes, String no) {
        String answer;
        do {
            System.out.print(prompt);
            try (Scanner in = new Scanner(System.in)) {
                answer = in.hasNextLine() ? in.nextLine() : null;
            }
        } while (answer == null || (!answer.equals(yes) && !answer.equals(no)));
        return answer.equals(yes);
    }

    /**
     * Resets the game. <br>
     * The board is emptied and player[0] becomes the current player.
     */
    private void reset() {
        current = 0;
        board.reset();
    }

    /**
     * Plays the Ringgz game. <br>
     * First the (still empty) board is shown. Then the game is played
     * until it is over. Players can make a move one after the other. 
     * After each move, the changed game situation is printed.
     */
    private void play() {
        System.out.println(board.toString());
        while(!board.boardIsFull()) {
        	int i = 0;
        	do {
        		i = players[current].determineMove(board);
        	} 
        	while(!board.isField(i)); //Not done
        	board.setField(i, players[current].getColor(), players[current].getColor()); //TODO get the Ring Choice in here
        	current += 1;
        	current %= 3;
        	update();
        }
        printResult();
    }

    /**
     * Prints the game situation.
     */
    private void update() {
        System.out.println("\ncurrent game situation: \n\n" + board.toString() + "\n");
    }

    /*@
       requires this.board.gameOver();
     */

    /**
     * Prints the result of the last game. <br>
     */
    private void printResult() {
        if (board.boardIsFull()) {
            for (int j = 0, j <= 4, j++) {
            	if players[j].getColor().(board.isWinner()) {
            		Player winner = players[j];
            	}
            }
            System.out.println("Player " + winner.getName() + " has won!");
        }
    }
}
