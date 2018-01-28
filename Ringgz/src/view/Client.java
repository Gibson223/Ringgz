package view;

import java.io.IOException;
import java.net.InetAddress;

import view.View.ViewState;
import server.Server;

//Creates a client
public class Client {

	// Creates a client for the game
	public static void main(String[] args) {
		View TUI = new TUI();
		new Thread(TUI).start();
		Game newClient = null;
		Object[] arguments = TUI.getArguments();
		TUI.setViewState(ViewState.CONNECTING);
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
