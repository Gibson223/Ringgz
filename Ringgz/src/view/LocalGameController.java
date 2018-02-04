package view;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;

import controller.HumanPlayer;
import controller.Move;
import controller.Player;
import controller.RinggzException;
import controller.ServerPlayer;
import model.Board;
import model.Color;
import model.Field;
import serverclient.Protocol;
import serverclient.Protocol.Packets;

public class LocalGameController implements Runnable {
	private final BufferedReader dis;
	private final PrintWriter dos;
	private InetAddress address;
	private Socket socket = null;
	private boolean gamerunning;
	private boolean connected;
	private final TUI tui;
	private final int port;
	private int playerAmount;
	private String playerType;
	private boolean leftLobby;
	private ArrayList<Player> players;
	private Board board;
	private String username;

	public LocalGameController(TUI tui, String username, InetAddress address, int port) throws IOException {
		this.players = new ArrayList<Player>();
		this.board = new Board();
		this.username = username;
		this.port = port;
		this.address = address;
		this.gamerunning = false;
		this.connected = false;
		this.tui = tui;
		this.socket = new Socket(address, port);
		this.dis = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
		this.dos = new PrintWriter(socket.getOutputStream(), true);
		this.sendMessage(Protocol.Packets.CONNECT + Protocol.DELIMITER + this.username);
		canmove = new Boolean[this.players.size()];
		// new Thread(this).start();
	}

	private void handleMessage(String message) {
		String[] messageparts = message.split(Protocol.DELIMITER);
		System.out.println(message);
		String feedback = null;
		String packetHeader = messageparts[0];
		if (Packets.CONNECT.equals(packetHeader)) {
			if (messageparts.length == 2 && messageparts[1].equals(Protocol.ACCEPT)) {
				// message in tui
				this.connected = true;
				feedback = this.tui.TUIInput("Please input the preffered amount of player and type of player " + "\n("
						+ Protocol.HUMAN_PLAYER + "for humanplayer" + ")\n(Separated by a space...)");
				int amount = Integer.parseInt(feedback.split(" ")[0]);
				String playerType = feedback.split(" ")[1];
				if (amount < 5 || amount > 1) {
					this.playerAmount = amount;
				} else {
					tui.output("Windows will now update");
					this.shutDown();
				}
				if (Protocol.HUMAN_PLAYER.equals(playerType)) {
					this.playerType = Protocol.HUMAN_PLAYER;
				} else {
					this.playerType = Protocol.COMPUTER_PLAYER;
				}
				this.sendMessage(Packets.GAME_REQUEST + Protocol.DELIMITER + this.playerAmount + Protocol.DELIMITER
						+ this.playerType);
			} else {
				feedback = this.tui.TUIInput("the server has denied your connection request\nPress 1 to reconnect");
				if (Integer.parseInt(feedback) == 1) {
					while (true) {
						try {
							new LocalGameController(this.tui, this.username, this.address, this.port);
						} catch (IOException e) {
							e.printStackTrace();
						}
					}
				} else {
					tui.output("Connection declined");
					this.shutDown();
				}
			}
		} else if (Protocol.Packets.JOINED_LOBBY.equals(packetHeader)) {
			if (!this.leftLobby) {
				tui.output("You have joined a lobby");
				this.leftLobby = true;
			} else {
				tui.output("Someone left your lobby");
				this.leftLobby = false;
			}
		} else if (Protocol.Packets.ALL_PLAYERS_CONNECTED.equals(packetHeader)) {
			ArrayList<String> playerNames = new ArrayList<String>();
			String playerName1 = messageparts[1];
			String playerName2 = messageparts[2];
			playerNames.add(playerName1);
			playerNames.add(playerName2);
			if (messageparts[3] != null) {
				String playerName3 = messageparts[3];
				playerNames.add(playerName3);
			}
			if (messageparts[4] != null) {
				String playerName4 = messageparts[4];
				playerNames.add(playerName4);
			}
			for (String player : playerNames) {
				if (this.username == player) {
					Player self = new HumanPlayer(player);
					players.add(self);
				} else {
					Player tempplayer = new ServerPlayer(player);
					players.add(tempplayer);
				}

			}
			this.sendMessage(Protocol.Packets.PLAYER_STATUS + Protocol.DELIMITER + Protocol.ACCEPT);
			tui.output("All players connected!!!");
		} else if (Protocol.Packets.GAME_STARTED.equals(packetHeader)) {
			this.play();
		} else if (Protocol.Packets.MOVE.equals(packetHeader)) {
			try {
				((ServerPlayer) this.players.get(currentplayer)).setMove(new Move(Integer.parseInt(messageparts[1]),
						Integer.parseInt(messageparts[2]), Integer.parseInt(messageparts[3]), messageparts[5]));
			} catch (NumberFormatException | IndexOutOfBoundsException e) {
			}
		}
	}

	private int currentplayer = 0;
	Boolean[] canmove;
	public void play() {
		boolean succes = false;
		while (!this.board.boardIsFull() || !Arrays.asList(canmove).stream().noneMatch(a -> a.booleanValue() == true)) {
			while (!succes) {
				try {
					if (players.get(currentplayer).playerCheck(this.board)) {
						players.get(currentplayer).makeMove(this.board);
						canmove[currentplayer] = false;
						succes = true;
					} else {
						canmove[currentplayer] = false;
						succes = true;
					}
				} catch (RinggzException e) {
					succes = false;
				}
			}
			currentplayer += 1;
			currentplayer %= this.players.size();
			succes = false;
		}
		Player winner = null;
		Color colorwin = this.board.isWinner();
		if (this.players.size() == 2) {
			Player one = this.players.get(0);
			Player two = this.players.get(1);
			for (Field field : this.board.fields) {
				if (field.isWinner() == Color.BLUE) {
					Color.BLUE.colorWonFields += 1;
				} else if (field.isWinner() == Color.RED) {
					Color.RED.colorWonFields += 1;
				} else if (field.isWinner() == Color.YELLOW) {
					Color.YELLOW.colorWonFields += 1;
				} else {
					Color.GREEN.colorWonFields += 1;
				}
			}
			one.playerScore = one.getPrimaryColor().colorWonFields + one.getSecondaryColor().colorWonFields;
			two.playerScore = two.getPrimaryColor().colorWonFields + two.getSecondaryColor().colorWonFields;
			if (one.playerScore > two.playerScore) {
				winner = one;
			} else if (two.playerScore > one.playerScore) {
				winner = two;
			} else if (one.playerScore == two.playerScore) {
				System.out.println("It's a tie!"); // aaaaa
			}
			System.out.println("The winner of the match is " + winner.getName());
		} else if (colorwin == null) {
			System.out.println("It is a tie....");
		} else {
			for (Player possiblewinner : this.players) {
				if (possiblewinner.getPrimaryColor() == colorwin) {
					winner = possiblewinner;
					break;
				}
			}
			System.out.println("The winner of the match is " + winner.getName());
		}
	}

	private void shutDown() {
		try {
			this.dis.close();
			this.dos.close();
			this.socket.close();
		} catch (IOException e) {
			e.printStackTrace();
		}

	}

	private void sendMessage(String message) {
		this.dos.println(message);
		this.dos.flush();
	}

	@Override
	public void run() {
		while (true) {
			String message;
			try {
				message = this.dis.readLine();
				this.handleMessage(message);
			} catch (IOException e) {
				this.tui.output("error during connection");
				this.shutDown();
				e.printStackTrace();
			}

		}
	}
}
