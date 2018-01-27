package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;

import net.Protocol;

/**
 * Textual User Interface (TUI) for the Ringgz game.
 */
public class TUI implements View {

	public static final String EXIT = "exit";
	
	private ViewState viewState;
	
	/**
	 * Creates a Textual User Interface (TUI) using the given <code>Game</code>.
	 */
	public TUI() {
		setViewState(ViewState.STARTUP);
	}
	
	@Override
	public void displayStartupState() {
		print("Please insert your username and the server IP address <username> <ip>");
	}
	
	@Override
	public void displayConnectingState() {
		print("Connecting to the server...");
	}
	
	@Override
	public void displayConnectedState() {
		print("You are now connected to the server!");
		print("You can request a game: <player amount> <opponent preference>");
		print("The player amount can be either 2, 3 or 4 and the opponent preference is one of the following:");
		print("\"human\"");
		print("\"computer\"");
		print("leave the field empty, this indicates you have no opponent preference.");
	}
	
	@Override
	public void displayLobbyState() {
		// TODO Auto-generated method stub
	}
	
	@Override
	public void displayGameState() {
		// TODO Auto-generated method stub
	}
	
	@Override
	public void displayGameMovingState() {
		// TODO Auto-generated method stub
	}
	
	@Override
	public void displayPostGameState() {
		print("Game has finished");
	}
	
	@Override
	public void displayError(String error) {
		print("[ERROR] " + error);
	}
	
	@Override
	public void run() {
		// do anything.
	}

	@Override
	public void setViewState(ViewState viewState) {
		this.viewState = viewState;
		switch(this.viewState) {
		case STARTUP:
			displayStartupState();
			break;
		case CONNECTING:
			displayConnectingState();
			break;
		case CONNECTED:
			displayConnectedState();
			break;
		case LOBBY:
			displayLobbyState();
			break;
		case GAME:
			displayGameState();
			break;
		case GAME_MOVING:
			displayGameMovingState();
			break;
		case POST_GAME:
			displayPostGameState();
			break;
		}
	}

	@Override
	public ViewState getViewState() {
		return this.viewState;
	}
	
	@Override
	public Object[] getArguments() {
		InetAddress ipAddress = null;
		String username = null;
		boolean valid = false;
		while(!valid) {
			valid = true;
			String input = readString(" > ");
			String[] args = input.split(" ");
			if(args.length != 2) {
				valid = false;
				print("Not enough arguments given (need 2). Please try again.");
				continue;
			}
			username = args[0];
			if(username.contains(";")) {
				valid = false;
				print("Username may not contain a semicolon (;). Please try again.");
				continue;
			}
			try {
				ipAddress = InetAddress.getByName(args[1]);
			} catch (UnknownHostException e) {
				valid = false;
				print("Given IP address is invalid. Please try again.");
				continue;
			}
		}
		return new Object[] {ipAddress, username};
	}

	@Override
	public void onConnectionAccepted() {
		setViewState(ViewState.CONNECTED);
	}
	
	@Override
	public void onConnectionDeclined() {
		print("Server did not accept connection.");
	}
	
	@Override
	public Object[] getGameRequest() {
		int playerAmount = 0;
		String opponentPref = null;
		boolean valid = false;
		while(!valid) {
			valid = true;
			String input = readString(" > ");
			String[] args = input.split(" ");
			if(args.length < 1 || args.length > 2) {
				valid = false;
				print("Not the right numbe of arguments given (need at lest 1, maximum of 2). Please try again.");
				continue;
			}
			try {
				playerAmount = Integer.parseInt(args[0]);
			} catch(NumberFormatException e) {
				valid = false;
				print("First argument is not a number. Please try again.");
				continue;
			}
			if(args.length == 2 && args[1].equals("human")) {
				opponentPref = Protocol.HUMAN_PLAYER;
			} else if(args.length == 2 && args[1].equals("computer")) {
				opponentPref = Protocol.COMPUTER_PLAYER;
			} if(args.length == 2) {
				valid = false;
				print("Second argument was not equal to \"human\" or \"computer\"");
				continue;
			}
		}
		if(opponentPref == null) {
			return new Object[] {playerAmount};
		} else {
			return new Object[] {playerAmount, opponentPref};
		}
	}

	@Override
	public void waitingInLoby() {
		print("Joined a lobby!");
	}
	
	@Override
	public boolean allPlayersConnected() {
		print("All players connected, are you ready? You have ten seconds to respond. (y/n)");
		return false;
	}
	
	@Override
	public void onGameStarted() {
		print("Game started!");
	}

	@Override
	public void otherMoves() {
		print("Waiting for other player(s)");
	}

	@Override
	public void gameFinished() {
		setViewState(ViewState.POST_GAME);
	}
	
	public static String readString(String text) {
		System.out.print(text);
		String antw = null;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			antw = in.readLine();
		} catch (IOException e) {
		}
		return (antw == null) ? "" : antw;
	}
	
	private static void print(String message){
		System.out.println(message);
	}
}