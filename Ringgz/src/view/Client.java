package view;

import java.io.IOException;
import java.net.InetAddress;

import view.View.ViewType;
import server.Server;

//Creates a client
public class Client {

	// Creates a client for the game
	//Takes a the IP adress and the username from the arguments
	public static void main(String[] args) {
		View TUI = new TUI();
		new Thread(TUI).start();
		Game newClient = null;
		Object[] arguments = TUI.getArguments();
		TUI.setViewType(ViewType.CONNECTING);
		InetAddress IP = (InetAddress) arguments[0];
		String username = (String) arguments[1];
		int port = Server.PORT;

		boolean success = false;
		while (!success) {
			try {
				success = true;
				newClient = new Game(TUI, username, IP, port);
				new Thread(newClient).start();
			} catch (IOException e) {
				success = false;
			}
		}
		newClient.sendMessage(username);
	}
}
