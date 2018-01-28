package view;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;

import net.Protocol;
import net.Protocol.Extensions;
import net.Protocol.Packets;
import net.ProtocolException;

/**
 * The <code>Game</code> class, which is responsible for making the game
 * function like it should. It will keep track of all <code>Player</code>s and
 * the <code>Move</code>s that they make.
 */
public class Game implements Runnable {

	private final BufferedReader in;
	private final BufferedWriter out;
	private final Socket socket;
	private final String clientName;
	private final View view;

	public Game(View view, String clientName, InetAddress host, int port) throws IOException {
		this.view = view;
		this.clientName = clientName;
		this.socket = new Socket(host, port);
		this.in = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
		this.out = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream(), "UTF-8"));
		sendMessage(Protocol.Packets.CONNECT + Protocol.DELIMITER + this.clientName + Protocol.DELIMITER
				+ Extensions.EXTENSION_CHATTING);
	}

	@Override
	public void run() {
		try {
			while (true) {
				String msg = in.readLine();
				processPacket(msg.split(Protocol.DELIMITER));
			}
		} catch (IOException e) {
			shutdown();
		} catch (ProtocolException e) {
			view.Error(e.getMessage());
			shutdown();
		}
	}

	private void processPacket(String[] data) throws ProtocolException {
		String packetType = data[0];
		switch (packetType) {

		case Packets.CONNECT:
			if (data.length >= 2) {
				if (data[1].equals(Protocol.ACCEPT)) {
					view.onConnectionAccepted();
					Object[] args = view.getGameRequest();
					if (args.length == 1) {
						sendMessage(Packets.GAME_REQUEST + Protocol.DELIMITER + args[0] + Protocol.DELIMITER
								+ Protocol.HUMAN_PLAYER);
					} else {
						sendMessage(Packets.GAME_REQUEST + Protocol.DELIMITER + args[0] + Protocol.DELIMITER
								+ Protocol.HUMAN_PLAYER + Protocol.DELIMITER + args[1]);
					}
				} else {
					view.onConnectionDeclined();
					shutdown();
				}
			} else {
				throw new ProtocolException("Cannot connect.");
			}
			break;
			
		case Packets.ALL_PLAYERS_CONNECTED:
			view.allPlayersConnected();
			String input = TUI.readString("");
			if (input.equals("y")) {
				sendMessage(Packets.PLAYER_STATUS + Protocol.DELIMITER + Protocol.ACCEPT);
			} else {
				sendMessage(Packets.PLAYER_STATUS + Protocol.DELIMITER + Protocol.DECLINE);
			}
			break;


		case Packets.JOINED_LOBBY:
			view.waitingInLobby();
			break;

		case Packets.GAME_STARTED:
			view.onGameStarted();
			break;

		default:
			break;
		}
	}

	public void sendMessage(String msg) {
		try {
			out.write(msg + "\n");
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	public void shutdown() {
		try {
			in.close();
			out.close();
			socket.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}