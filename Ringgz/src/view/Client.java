package view;

import controller.HumanPlayer;
import controller.GameController;
import controller.ComputerPlayer;
import controller.Player;

public class Client {
	public static void main(String[] args) {
		localGame();
	}
	public static void localGame() {
		Player gibson = new ComputerPlayer("a");
		Player random = new ComputerPlayer("b");
		Player geez = new HumanPlayer("c");
		Player nuller = new HumanPlayer("d");
		GameController gc = new GameController(gibson, random, null, null);
		Thread game = new Thread(gc);
		game.start();
	}
//	public static void main(String[] args) {
//		System.out.println("please type in a name, 
//	inetaddress and portnumber.....\n(separated by a space)");
//		Scanner in = new Scanner(System.in);
//		String name = in.nextLine().split(" ")[0];
//        try {
//			InetAddress addr = InetAddress.getByName(in.nextLine().split(" ")[1]);
//		} catch (UnknownHostException e) {
//			System.out.println("wrong adress");
//			e.printStackTrace();
//		}
//        int port = Integer.parseInt(in.nextLine().split(" ")[2]);
//		;
//		Socket client = new Socket();
//	}

}
