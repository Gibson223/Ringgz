package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Observable;
import model.*;
import controller.*;

import net.Protocol;

//TUI for Ringgz
public class TUI implements View {

	private Board board;

	public static final String EXIT = "exit";

	private ViewState viewState;

	// Creates a TUI with the given Game
	public TUI() {
		setViewState(ViewState.STARTUP);
	}

	@Override
	public void displayStartupState() {
		print("Insert username and IP separated by a space");
	}

	@Override
	public void displayConnectingState() {
		print("Connecting...");
	}

	@Override
	public void displayConnectedState() {
		print("You are connected.");
		print("To request a game: <player amount> <opponent preference>");
		print("The player amount can be either 2, 3 or 4 and the opponent preference is either /human/ or /computer/");
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
	public void setViewState(ViewState viewState) {
		this.viewState = viewState;
		switch (this.viewState) {
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
		while (!valid) {
			valid = true;
			String input = readString(" > ");
			String[] args = input.split(" ");
			if (args.length != 2) {
				valid = false;
				print("Two arguments are needed. Please try again.");
				continue;
			}
			username = args[0];
			if (username.contains(";")) {
				valid = false;
				print("A username cannot contain a semicollon. Please try again.");
				continue;
			}
			try {
				ipAddress = InetAddress.getByName(args[1]);
			} catch (UnknownHostException e) {
				valid = false;
				print("Invalid IP. Please try again.");
				continue;
			}
		}
		return new Object[] { ipAddress, username };
	}

	@Override
	public void onConnectionAccepted() {
		setViewState(ViewState.CONNECTED);
	}

	@Override
	public void onConnectionDeclined() {
		print("Server denied connection.");
	}

	@Override
	public Object[] getGameRequest() {
		int playerAmount = 0;
		String opponentPref = null;
		boolean valid = false;
		while (!valid) {
			valid = true;
			String input = readString(" > ");
			String[] args = input.split(" ");
			if (args.length < 1 || args.length > 2) {
				valid = false;
				print("Not the right number of arguments given.");
				continue;
			}
			try {
				playerAmount = Integer.parseInt(args[0]);
			} catch (NumberFormatException e) {
				valid = false;
				print("First argument is not a number. Please try again.");
				continue;
			}
			if (args.length == 2 && args[1].equals("human")) {
				opponentPref = Protocol.HUMAN_PLAYER;
			} else if (args.length == 2 && args[1].equals("computer")) {
				opponentPref = Protocol.COMPUTER_PLAYER;
			}
			if (args.length == 2) {
				valid = false;
				print("Second argument was not equal to \"human\" or \"computer\"");
				continue;
			}
		}
		if (opponentPref == null) {
			return new Object[] { playerAmount };
		} else {
			return new Object[] { playerAmount, opponentPref };
		}
	}

	@Override
	public void waitingInLobby() {
		print("Joined a lobby!");
	}

	@Override
	public boolean allPlayersConnected() {
		print("All players connected, are you ready? (y/n)");
		return false;
	}

	@Override
	public void onGameStarted() {
		print("The game has started!");
	}

	@Override
	public void otherMoves() {
		print("Waiting for other players");
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

	private static void print(String message) {
		System.out.println(message);
	}

	public void run() {
		//
	}
}