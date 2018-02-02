package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.net.InetAddress;

import controller.GameController;
import server.Server;
import serverclient.Protocol.Packets;
import serverclient.ProtocolException;

//Creates a client
public class Client {

	// Creates a client for the game
	public static void main(String[] args) throws IOException {
		TUI tui = new TUI();
		Object[] input = tui.initizializing();
		String username = (String) input[0];
		InetAddress ip = (InetAddress) input[1];
		int port = Server.PORT;
		LocalGameController gc = new LocalGameController(tui, username, ip, port);//TODO does need work to work
		new Thread(gc).start(); 
	}
	}

