package controller;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.RingList;
import model.Tier;
import serverclient.ClientHandler;
import serverclient.Protocol;
import serverclient.Server;
import serverclient.Protocol.Packets;
import view.TUI;

public class GameController implements Runnable {
    public List<Player> players;
    public Board board;
    public TUI tui;
    public RingList ringlist;
    public int maxplayers;
    public List<ClientHandler> clients;
    private Server server;
    public boolean started;
    public final int ALLOWEDDELAY = 20000;

    /**
     * Starts the game controller.
     *
     * @param server
     *            the server this gamecontroller will play in
     * @param maxplayers
     *            the maximum amount of players for the lobby
     * 
     */
    public GameController(Server server, int maxplayers) {
        this.server = server;
        this.maxplayers = maxplayers;
        this.clients = new ArrayList<>();
        this.players = new ArrayList<>();

    }

    /**
     * Starts the game.
     */
    public void run() {
        try {
            while (!this.startGame()) {
                try {
                    this.startgame();
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        } catch (InterruptedException | IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Creates a game controller for three players.
     *
     * @param s0
     *            the first player
     * @param s1
     *            the second player
     * @param s2
     *            the third player
     */
    public GameController(Player s0, Player s1, Player s2) {
        this(s0, s1, s2, null);
    }

    /**
     * Creates a game controller for two players.
     *
     * @param s0
     *            the first player
     * @param s1
     *            the second player
     */
    public GameController(Player s0, Player s1) {
        this(s0, s1, null, null);
    }

    /**
     * Creates a game controller for four players.
     *
     * @param s0
     *            the first player
     * @param s1
     *            the second player
     * @param s2
     *            the third player
     * @param s3
     *            the fourth player
     */
    public GameController(Player s0, Player s1, Player s2, Player s3) {
        List<Object> playerlist = new ArrayList<>();
        List<ClientHandler> clients = new ArrayList<>();
        playerlist.add(s0);
        playerlist.add(s1);
        playerlist.add(s2);
        playerlist.add(s3);
        playerlist.stream().filter(a -> a != null).forEach(a -> players.add((Player) a));
        this.run();
    }

    /**
     * Starts a game for this GameController.
     *
     * @return true if the creation of the game is succesful, false otherwise.
     * 
     * @throws InterruptedException,
     *             IOException
     */
    private synchronized boolean startGame() throws InterruptedException, IOException {
        Collections.shuffle(clients);
        String usernames = "";
        for (ClientHandler client : this.clients) {
            usernames = usernames + Protocol.DELIMITER + client.username;
        }
        for (ClientHandler client : this.clients) {
            client.sendmessage(Packets.ALL_PLAYERS_CONNECTED + usernames);
        }
        long start = System.currentTimeMillis();
        while (!this.clients.stream().allMatch(a -> a.getResponded() == true)) {
            long current = System.currentTimeMillis();
            if (current - start < ALLOWEDDELAY) {
                wait();
            }
        }
        if (!already()) {
            for (ClientHandler client : this.clients) {
                if (!client.getResponded() || !client.getReady()) {
                    removeClient(client);
                }
            }
            for (ClientHandler client : this.clients) {
                client.sendmessage(Packets.JOINED_LOBBY);
            }
            return false;
        } else {
            for (ClientHandler client : this.clients) {
                client.sendmessage(Packets.GAME_STARTED);
            }
            return true;
        }
    }

    /**
     * Returns whether the GameController already exists.
     *
     * @return true if the gc already exists, false otherwise.
     */
    private boolean already() {
        for (ClientHandler handler : this.clients) {
            if (!handler.getResponded() || !handler.getReady()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Adds a player to the client handler.
     *
     * @param handler
     *            The client handler in question
     * @return true if the adding of the player was succesful, false otherwise.
     */
    public synchronized boolean addPlayer(ClientHandler handler) {
        if (!this.started && this.clients.size() < this.maxplayers) {
            this.clients.add(handler);
            notify();
            return true;
        } else {
            return false;
        }
    }

    /**
     * Begins the game.
     * 
     * @throws IOException
     */
    public void startgame() throws IOException {
        board = new Board();
        ringlist = new RingList();
        this.playerSetter();
        this.ringdivider();
        this.play();

    }

    /**
     * Sets the primary and secondary colors depending on the number of players.
     */
    private void playerSetter() {
        if (this.players.size() == 2) {
            players.get(0).setPrimary(Color.RED);
            players.get(0).setSecondary(Color.YELLOW);
            players.get(1).setPrimary(Color.GREEN);
            players.get(1).setSecondary(Color.BLUE);
        }
        if (this.players.size() == 3) {
            players.get(0).setPrimary(Color.RED);
            players.get(1).setPrimary(Color.YELLOW);
            players.get(2).setPrimary(Color.GREEN);
            players.get(0).setSecondary(Color.BLUE);
            players.get(1).setSecondary(Color.BLUE);
            players.get(2).setSecondary(Color.BLUE);
        }
        if (this.players.size() == 4) {
            players.get(0).setPrimary(Color.RED);
            players.get(1).setPrimary(Color.YELLOW);
            players.get(2).setPrimary(Color.GREEN);
            players.get(3).setPrimary(Color.BLUE);
        }
    }

    /**
     * Divides the rings for the players depending on the total number of players.
     */
    private void ringdivider() {
        if (this.players.size() == 2) {
            RingList ringlistpart1 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(0, 30)));
            RingList ringlistpart2 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(30, 60)));
            players.get(0).setRingList(ringlistpart1);
            players.get(1).setRingList(ringlistpart2);
        }
        if (this.players.size() == 3) {
            RingList ringlistpart1 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(0, 15)));
            RingList ringlistpart2 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(15, 30)));
            RingList ringlistpart3 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(30, 45)));
            ringlistpart1.availableRings
                    .addAll(new ArrayList<Ring>(ringlist.availableRings.subList(45, 50)));
            ringlistpart2.availableRings
                    .addAll(new ArrayList<Ring>(ringlist.availableRings.subList(50, 55)));
            ringlistpart3.availableRings
                    .addAll(new ArrayList<Ring>(ringlist.availableRings.subList(55, 60)));
            players.get(0).setRingList(ringlistpart1);
            players.get(1).setRingList(ringlistpart2);
            players.get(2).setRingList(ringlistpart3);
        }
        if (this.players.size() == 4) {
            RingList ringlistpart1 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(0, 15)));
            RingList ringlistpart2 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(15, 30)));
            RingList ringlistpart3 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(30, 45)));
            RingList ringlistpart4 = new RingList(
                    new ArrayList<Ring>(ringlist.availableRings.subList(45, 60)));
            players.get(0).setRingList(ringlistpart1);
            players.get(1).setRingList(ringlistpart2);
            players.get(2).setRingList(ringlistpart3);
            players.get(3).setRingList(ringlistpart4);
        }

    }

    private int currentplayer = 0;

    /**
     * Checks if a move is valid.
     *
     * @return true if the move is valid, false otherwise.
     */
    public boolean checkMove(Move move) {
        if (move == null) {
            return false;
        }
        int choiceField = board.index(move.getX() + 1, move.getY() + 1);
        Tier choiceRing = move.getMoveType();
        Color choiceColor;
        if (Protocol.SECONDARY.equals(move.getColor())) {
            choiceColor = this.players.get(currentplayer).getSecondaryColor();
        } else {
            choiceColor = this.players.get(currentplayer).getPrimaryColor();
        }
        if (board.firstMove) {
            if (board.middle9.stream().anyMatch(a -> a == choiceField)) {
                try {
                    this.board.getField(choiceField).placeBase();
                } catch (RinggzException e) {
                    return false;
                }
                this.board.firstMove = false;
                return true;
            } else {
                return false;
            }
        } else {
            Ring selectedRing = new Ring(choiceColor, choiceRing);
            try {
                if (board.isAllowed(choiceField, selectedRing)
                        && board.proximityCheck(choiceField,
                                players.get(currentplayer).getPrimaryColor())
                        || board.fieldHasColor(choiceField,
                                players.get(currentplayer).getPrimaryColor())
                                && this.players.get(currentplayer).ringList.availableRings
                                        .contains(selectedRing)) {
                    board.setRing(choiceField, selectedRing);
                    this.players.get(currentplayer).ringList.availableRings.remove(selectedRing);
                    return true;
                } else {
                    return false;
                }
            } catch (RinggzException e) {
                return false;
            }
        }
    }

    /**
     * Keeps track of the gameplay and the moves in particular.
     * 
     * @throws IOException
     */
    private void play() throws IOException {
        Boolean[] canmove = new Boolean[this.players.size()];
        boolean succes = false;
        while (!this.board.boardIsFull()
                || !Arrays.asList(canmove).stream().noneMatch(a -> a.booleanValue() == true)) {
            while (!succes) {
                try {
                    if (players.get(currentplayer).playerCheck(this.board)) {
                        Move currentMove = players.get(currentplayer).makeMove(this.board);
                        if (this.checkMove(currentMove)) {
                            canmove[currentplayer] = false;
                            succes = true;
                        } else {
                            currentplayer -= 1;
                        }
                    } else {
                        canmove[currentplayer] = false;
                        succes = true;
                    }
                } catch (RinggzException e) {
                    succes = false;
                }
            }
            this.clients.get(currentplayer).sendmessage(Protocol.Packets.MAKE_MOVE);
            currentplayer += 1;
            currentplayer %= this.players.size();
            succes = false;
        }
        int colorBLUEcolorWonFields = 0;
        int colorREDcolorWonFields = 0;
        int colorYELLOWcolorWonFields = 0;
        int colorGREENcolorWonFields = 0;
        for (Field field : this.board.fields) {
            if (field.isWinner() == Color.BLUE) {
                colorBLUEcolorWonFields += 1;
            } else if (field.isWinner() == Color.RED) {
                colorREDcolorWonFields += 1;
            } else if (field.isWinner() == Color.YELLOW) {
                colorYELLOWcolorWonFields += 1;
            } else {
                colorGREENcolorWonFields += 1;
            }
        }
        String message = Protocol.Packets.GAME_ENDED + Protocol.DELIMITER;
        if (this.players.size() == 2) {
            Player one = this.players.get(0);
            Player two = this.players.get(1);
            one.playerScore = one.getPrimaryColor().colorWonFields
                    + one.getSecondaryColor().colorWonFields;
            two.playerScore = two.getPrimaryColor().colorWonFields
                    + two.getSecondaryColor().colorWonFields;
            message = message + players.get(0).getName() + Protocol.DELIMITER + one.playerScore
                    + Protocol.DELIMITER + players.get(1).getName() + Protocol.DELIMITER
                    + two.playerScore;
        } else {
            message = message + players.get(0).getName() + Protocol.DELIMITER
                    + colorREDcolorWonFields + Protocol.DELIMITER + players.get(1).getName()
                    + Protocol.DELIMITER + colorYELLOWcolorWonFields + Protocol.DELIMITER
                    + players.get(2).getName() + Protocol.DELIMITER + colorGREENcolorWonFields
                    + Protocol.DELIMITER;
            if (players.size() == 4) {
                message = message + players.get(3).getName() + Protocol.DELIMITER
                        + colorBLUEcolorWonFields;
            }
        }
        this.server.serverPrint(message);
        for (ClientHandler ch : this.clients) {
            ch.sendmessage(message);
        }
    }

    /**
     * Adds a client to the clientHandler.
     * 
     * @return true if successful, false otherwise.
     */
    public synchronized boolean addClient(ClientHandler ch) {
        if (this.players.size() < this.maxplayers && this.started == false) {
            this.clients.add(ch);
            ch.linkedgame = this;
            return true;
        } else {
            return false;
        }
    }

    /**
     * Removes a client from the clientHandler.
     * 
     * @return true if successful, false otherwise.
     */
    public synchronized void removeClient(ClientHandler ch) {
        ch.linkedgame = null;
        this.clients.remove(ch);
    }
}
