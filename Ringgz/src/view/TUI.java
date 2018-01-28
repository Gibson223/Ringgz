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
	public void StartupState() {
		print("Insert username and IP separated by a space");
	}

	@Override
	public void ConnectingState() {
		print("Connecting...");
	}

	@Override
	public void ConnectedState() {
		print("You are connected.");
		print("To request a game: <player amount> <opponent preference>");
		print("Player amount options: 2, 3 or 4");
		print("Opponent preference options: /human/ or /computer/");
	}

	@Override
	public void PostGameState() {
		print("Game over");
	}

	@Override
	public void Error(String error) {
		print("[ERROR] " + error);
	}

	@Override
	public void setViewState(ViewState viewState) {
		this.viewState = viewState;
		switch (this.viewState) {
		case STARTUP:
			StartupState();
			break;
		case CONNECTING:
			ConnectingState();
			break;
		case CONNECTED:
			ConnectedState();
			break;
		case POST_GAME:
			PostGameState();
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
	public void awaitingMoves() {
		print("Waiting for other players to make their move...");
	}

	@Override
	public void gameFinished() {
		setViewState(ViewState.POST_GAME);
	}

	public static String readString(String text) {
		System.out.print(text);
		String answer = null;
		try {
			BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
			answer = in.readLine();
		} catch (IOException e) {
		}
		return (answer == null) ? "" : answer;
	}

	private static void print(String message) {
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
		Board b = new Board();
		Ring ring = new Ring(Color.BLUE, Tier.BASE);
		Ring ring1 = new Ring(Color.GREEN, Tier.BASE);
		Ring ring2 = new Ring(Color.BLUE, Tier.BASE);
		Ring ring3 = new Ring(Color.BLUE, Tier.BASE);
		try {
			b.setRing(2, ring);
			b.setRing(4, ring1);
			b.setRing(6, ring2);
			b.setRing(8, ring3);
		} catch (RinggzException e) {
		}
		this.start();

	}

	public void start() {
		this.view();
	}
}