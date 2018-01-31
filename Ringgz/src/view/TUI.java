package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.Observer;

import model.*;
import serverclient.Protocol;
import controller.*;

//TUI for Ringgz
public class TUI implements Observer, Runnable {

	private Board board;

	public static final String EXIT = "exit";

	// Creates a TUI with the given Game
	public TUI() {
<<<<<<< Upstream, based on origin/master
		setViewType(ViewType.START);
=======
		this.INIT();
//		this.initizializing();
>>>>>>> eb5b220 did my best but i just got to go to bed.
	}

	public void INIT() {
		clientPrint("Insert username and IP separated by a space");
	}

	public void Connecting() {
		clientPrint("Connecting...");
	}

	public void Connected() {
		clientPrint("You are connected.");
		clientPrint("To request a game: <player amount> <opponent preference>");
		clientPrint("Player amount options: 2, 3 or 4");
		clientPrint("Opponent preference options: /human/ or /computer/");
	}
	
	public void GameOver() {
		clientPrint("The game has finished");
	}

//	public void Error(String error) {
//		print("[ERROR] " + error);
//	}

<<<<<<< Upstream, based on origin/master
	@Override
	public void setViewType(ViewType type) {
		this.type = type;
		switch (this.type) {
		case START:
			Initial();
			break;
		case CONNECTING:
			Connecting();
			break;
		case CONNECTED:
			Connected();
			break;
		case POST_GAME:
			GameOver();
			break;
		}
	}

	@Override
	public ViewType getViewType() {
		return this.type;
	}

	@Override
	public Object[] getArguments() {
		InetAddress ipAddress = null;
=======
	public Object[] initizializing() {
		String username = null;
		InetAddress address = null;
		boolean correct = false;
		while (!correct) {
			Object input = TUI.TUIInput("-");
			Object[] splitInput = ((String) input).split(" ");
			correct = true;
			if (splitInput.length != 2) {
				correct = false;
				clientPrint("Two arguments are needed. Please try again.");
				continue;//why not a break??
			}
			username = (String) splitInput[0];
			try {
				address = InetAddress.getByName((String) splitInput[1]);
			} catch (UnknownHostException e) {
				correct = false;
				clientPrint("Unable to connect.....\nTry again");
				continue;
			}
		}
		return new Object[] { username, address };
	}

	@Override
	public void accepted() {
		setViewType(ViewType.CONNECTED);
=======
	public void onConnectionAccepted() {
		this.Connected();
>>>>>>> eb5b220 did my best but i just got to go to bed.
	}

	@Override
	public void denied() {
		print("Server denied connection.");
		
	public void onConnectionDeclined() {
		clientPrint("Server denied connection.");
	}

	public void inLobby() {
		clientPrint("Joined a lobby!");
	}

	public boolean allConnected() {
		clientPrint("All players connected, are you ready? (y/n)");
		return false;
	}

	@Override
	public void startGame() {
		print("The game has started!");
	public void onGameStarted() {
		clientPrint("The game has started!");
		this.view();
	}

	public void awaitingMoves() {
		clientPrint("Waiting for other players to make their move...");
	}
	//TODO gamefinished message
	public void gameFinished() {
		this.clientPrint("the game has finished");
	}

	public static String TUIInput(String string) {
		String response = null;
		System.out.println(string);
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			response = in.readLine();
		} catch (IOException e) {}
		if (response == null ) {
			return TUI.TUIInput(string);
		} else {
			return response;
		}
	}		
	
//	public static String readString(String text) {
//		System.out.print(text);
//		String answer = null;
//		try {
//			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
//			answer = in.readLine();
//		} catch (IOException e) {
//		}
//		return (answer == null) ? "" : answer;
//	}

	private void clientPrint(String message) {
		System.out.println(message);
	}

	public void view() {
		for (Field field : board.fields) {
			if (((field.FieldNumber - 1) % 5) == 0) {
				System.out.print("\n\n" + "|");
			}
			System.out.print(field.toString() + "|");
		}
	}
	public void run() {
		this.view();
	}


	@Override
	public void update(Observable arg0, Object arg1) {	
		this.view();
	}
}