package view;

import controller.ComputerPlayer;
import controller.GameController;
import controller.HumanPlayer;
import controller.Player;

public class Client {
	public static void main(String[] args) {
		localGame();
	}
	public static void localGame() {
		Player gibson = new ComputerPlayer("gibson");
		Player random = new HumanPlayer("random");
		Player geez = new HumanPlayer("geezer");
		Player nuller = new HumanPlayer("null");
		GameController gc = new GameController(gibson, random, geez, null);
		Thread game = new Thread(gc);
		game.start();
	}
//	public static void main(String[] args) {
//		System.out.println("please type in a name, inetaddress and portnumber.....\n(separated by a space)");
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
