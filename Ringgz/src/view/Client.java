package view;

import java.io.IOException;
import java.net.InetAddress;

import controller.GameController;
import view.View.ViewType;
import server.Server;

//Creates a client
public class Client {

	// Creates a client for the game
	public static void main(String[] args) {
		TUI tui = new TUI();
		
//		new Thread(TUI).start();
		
		Object[] input = tui.initizializing();
		String username = (String) input[0];
		InetAddress adress = (InetAddress) input[1];
		int port = Server.PORT;
		tui.Connecting();
		boolean startinggame = true;
		GameController gc  = null;
		while (startinggame) {
//			try {
				startinggame = false;
//				gc = new GameController(tui, username, ip, port);//TODO does need work to work
				new Thread(gc).start(); 
//			} catch (IOException e) {
				startinggame = true;
			}
		}
//		newClient.sendMessage(username);//TODO put in client itself
	}

