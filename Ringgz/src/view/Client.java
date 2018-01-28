package view;

import java.io.IOException;
import java.net.InetAddress;

import view.View.ViewState;
import server.Server;

//Creates a client
public class Client {

	/** Starts the client. */
	public static void main(String[] args) {
		View view = new TUI();
		new Thread(view).start();
		Game client = null;

		Object[] arguments = view.getArguments();
		view.setViewState(ViewState.CONNECTING);
		InetAddress ipAddress = (InetAddress) arguments[0];
		String username = (String) arguments[1];
		int port = Server.PORT;

		boolean connecting = true;
		while (connecting) {
			try {
				connecting = false;
				client = new Game(view, username, ipAddress, port);
				new Thread(client).start();
			} catch (IOException e) {
				connecting = true;
			}
		}
		client.sendMessage(username);
	}
}
