package serverclient;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.LinkedList;
import java.util.List;

import controller.GameController;

public class Server implements Runnable {
    public static int PORT = 1150;
    private ServerSocket server;
    private List<GameController> games;
    private List<ClientHandler> clients;
    private BufferedReader dis;
    private BufferedWriter dos;
    private boolean online;
    public final int WAIT = 10000;

    public Server() throws IOException {
        this.server = new ServerSocket(PORT);
        this.games = new LinkedList<GameController>();
        this.clients = new LinkedList<>();
        online = true;
    }

    // Starts the Server 
    public static void main(String[] args) {
        try {
            Server s = new Server();
            Thread sthread = new Thread(s);
            sthread.start();
            System.out.println("The server has been started.");
            System.out.println("the port is " + s.PORT);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void run() {
        this.acceptClientSockets();
        try {
            this.shutDown();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public void acceptClientSockets() {
        while (online) {
            try {
                Socket clientSocket = server.accept();
                ClientHandler clienthandler = new ClientHandler(this, clientSocket);
                new Thread(clienthandler).start();
                this.addHandler(clienthandler);
                System.out.println("Assigned new thread for client" + clientSocket);
            } catch (IOException e) {
            }
        }
    }

    public GameController getGame(ClientHandler ch, int preferredplayers) {
        if (this.games.size() != 0) {
            for (GameController gc : this.games) {
                if (gc.players.size() < gc.maxplayers && gc.addClient(ch)) {
                    gc.addPlayer(ch);
                    return gc;
                }
            }
        }
        GameController newgame = new GameController(this, preferredplayers);
        newgame.addClient(ch);
        new Thread(newgame).start();
        return newgame;
    }

    public void serverPrint(String s) {
        System.out.println(s);
    }

    public List<ClientHandler> getClients() {
        return clients;
    }

    private void addHandler(ClientHandler ch) {
        this.clients.add(ch);
    }

    private void removeHandler(ClientHandler ch) {
        this.clients.remove(ch);
    }

    // requires packet matches extension chatting
    public void serverMessage(String message) throws IOException {
        for (ClientHandler clienthandler : this.getClients()) {
            clienthandler.sendmessage(message);
        }
    }

    private void shutDown() throws IOException {
        this.dis.close();
        this.dos.close();
        this.server.close();
    }
}
