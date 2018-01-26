package view;

import controller.*;

public class Client {
	public static void main(String[] args) {
		localGame();
	}
	public static void localGame() {
		Player Gibson = new HumanPlayer("Gibson");
		Player Random = new HumanPlayer("Random");
		Player geez = new HumanPlayer("geezer");
		Player nuller = new HumanPlayer("null");
		GameController gc = new GameController(Gibson, Random, geez, null);
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
