package serverclient;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;

import controller.GameController;
import controller.Move;
import serverclient.Protocol.Packets;

public class ClientHandler implements Runnable {
    private BufferedReader dis;
    private PrintWriter dos;
    private Server server;
    private final Socket clientSocket;
    public String username;
    private boolean ready; // == ready
    private boolean responded; // == responded
    public GameController linkedgame;

    public boolean getReady() {
        return this.ready;
    }

    public boolean getResponded() {
        return this.getResponded();
    }

    // Constructor
    public ClientHandler(Server server, Socket clientSocket) throws IOException {
        this.username = null;
        this.server = server;
        this.clientSocket = clientSocket;
        this.dis = new BufferedReader(
                new InputStreamReader(clientSocket.getInputStream(), "UTF-8"));
        this.dos = new PrintWriter(clientSocket.getOutputStream(), true);
        ready = false;
        responded = false;
    }

    @Override
    public void run() {
        try {
            while (true) {
                String message = this.dis.readLine();
                this.server.serverPrint(message);
                String[] splitmessage = message.split(Protocol.DELIMITER);
                this.packetHandler(splitmessage);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        // todo splitter init message contains packettype, username

    }

    private void packetHandler(String[] fullpacket) throws IOException {
        String packet = fullpacket[0];
        if (Packets.CONNECT.equals(packet)) {
            this.server.serverPrint(fullpacket.toString());
            // dont understand why Connection already established so look for other data
            if (packet.equals(Packets.CONNECT) && this.username == null) {
                this.username = fullpacket[1];
                this.dos.println(Packets.CONNECT + Protocol.DELIMITER + Protocol.ACCEPT
                        + Protocol.DELIMITER);
                this.server.serverPrint("connect packet received");
            }
        } else if (Packets.GAME_REQUEST.equals(packet)) {
            try {
                int preferredplayers = Integer.parseInt(fullpacket[1]);
                this.linkedgame = this.server.getGame(this, preferredplayers);
                if (this.linkedgame != null) {
                    this.sendmessage(Protocol.Packets.JOINED_LOBBY);
                }
            } catch (NumberFormatException e) {
            }
            this.server.serverPrint("game request packet has numberformat error..");
        } else if (packet == Packets.PLAYER_STATUS) {
            if (this.linkedgame != null) {
                if (fullpacket.length >= 2 && fullpacket[1].equals(Protocol.ACCEPT)) {
                    this.responded = true;
                    this.ready = true;
                } else {
                    responded = false;
                }
                synchronized (this.linkedgame) {
                    this.linkedgame.notify();
                }
            }
        } else if (Packets.MOVE.equals(packet)) {
            try {
                if (this.linkedgame != null && this.linkedgame.started) {
                    this.move = new Move(Integer.parseInt(fullpacket[1]),
                            Integer.parseInt(fullpacket[2]), Integer.parseInt(fullpacket[3]),
                            fullpacket[5]);
                } else {
                    this.server
                            .serverPrint("client sending move package when not playing a game...");
                }
            } catch (NumberFormatException | IndexOutOfBoundsException e) {
                this.server.serverPrint("incorrect move Package received by " + this.username);
            }
        } else {
            this.server.serverPrint(
                    "unknown packet type received at clienthandler of " + this.username);
        }
    }

    private Move move;

    public Move getMove() {
        return this.move;
    }

    public void sendmessage(String message) throws IOException {
        this.dos.println(message);
        this.dos.flush();
    }

}
