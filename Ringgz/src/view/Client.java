package view;

import serverclient.*;
import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;

//Creates a client
public class Client {
	// Creates a client for the game
	public static final int PORT = Server.PORT;
	public static void main(String[] args) throws IOException {
		TUI tui = new TUI();
		Object[] input = tui.initizializing();
		String username = (String) input[0];
		int port = Integer.parseInt(tui.TUIInput("please give the port"));
		InetAddress address = (InetAddress.getByName((String) input[1]));
		LocalGameController gc = new LocalGameController(tui, username, address, port);
		new Thread(gc).run();
		System.out.println("gc started");
	}
}
