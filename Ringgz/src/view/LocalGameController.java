package view;

import java.awt.List;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.LinkedList;
import controller.Player;
import controller.ServerPlayer;
import controller.GameController;
import controller.HumanPlayer;
import serverclient.ProtocolException;
import serverclient.Server;
import serverclient.Protocol;
import serverclient.Protocol.Packets;

public class LocalGameController implements Runnable {
	private final BufferedReader dis;
	private final BufferedWriter dos;
	private final String username;
	private final Socket socket;
	private boolean gamerunning;
	private boolean connected;
	private final TUI tui;
	private final InetAddress ip;
	private final int port;
	private int playerAmount;
	private String playerType;
	private boolean leftLobby;
	private ArrayList<Player> players;
	private int self;

	public LocalGameController(TUI tui, String username, InetAddress ip, int port) throws IOException {
		this.players = new ArrayList<Player>();
		this.username = username;
		this.port = port;
		this.ip = ip;
		this.gamerunning = false;
		this.connected = false;
		this.tui = tui;
		this.socket = new Socket(ip, port);
		this.dis = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
		this.dos = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream(), "UTF-8"));
		this.sendMessage(Protocol.Packets.CONNECT + Protocol.DELIMITER + this.username);
	}

	private void handleMessage(String message) {
		String[] messageparts = message.split(Protocol.DELIMITER);
		String feedback = null;
		String packetHeader = messageparts[0];
		if (Packets.CONNECT.equals(packetHeader)) {
			if (messageparts.length == 2 && messageparts[1].equals(Protocol.ACCEPT)) {
				// message in tui
				this.connected = true;
				feedback = this.tui.TUIInput(
						"Please input the preffered amount of player and type of player \n ()\n(Separated by a space...)");
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
							new LocalGameController(this.tui, this.username, this.ip, this.port);
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
			this.startGame();
		}

	}

	private void startGame() {
		// TODO Auto-generated method stub
		
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
		try {
			this.dos.write(message);
		} catch (IOException e) {
			this.tui.output("Unable to send message:" + message);
			e.printStackTrace();
		}
	}

	@Override
	public void run() {
		this.sendMessage(this.username);
		while (!gamerunning) {
			String message;
			try {
				message = this.dis.readLine();
				this.handleMessage(message);
			} catch (IOException e) {
				this.tui.output("error during connection");
				e.printStackTrace();
			}

		}
	}
}
