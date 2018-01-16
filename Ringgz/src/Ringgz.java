/**
 * Executable class for the game Ringgz.
 * 
 * @author Inigo Artolozaga & Gibson Vredeveld
 */

public class Ringgz {
    public static void main(String[] args) {
    	Player[] player = new Player[4]; //WE HAVE TO ADD AN OPTION TO PLAY WITH 2, 3 OR 4 PLAYERS
    	for (int i = 0; i < args.length; i++) {
    		Color color = new Color.RED; //INITIALIZE THIS VALUE AS RED AND THEN ROTATE FOR NEXT PLAYERS
    		if (args[i].equals("-N")) {
    			player[i] = new ComputerPlayer(color, new NaiveStrategy());
    		} else {
    			if (args[i].equals("-S")) {
    				player[i] = new ComputerPlayer(color, new SmartStrategy());
    			} else {
    				player[i] = new HumanPlayer(args[i], color);
    			}
    		}
    		color.next(); //THIS IS WHAT ROTATES THE COLOR
    	}
        Game g = new Game(player[0], player[1],player[2],player[3]);
        g.start();
    }
}
