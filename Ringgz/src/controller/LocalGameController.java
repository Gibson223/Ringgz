package controller;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Arrays;

import model.Board;
import model.Color;
import model.Field;
import model.Ring;
import model.Tier;
import serverclient.Protocol;
import serverclient.Protocol.Packets;
import view.TUI;

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

    public LocalGameController(TUI tui, String username, InetAddress address, int port)
            throws IOException {
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
                    // this.tui.output("\nthe ring has been added to the field....");
                    return true;
                } else {
                    // this.tui.output("Invalid move, try another one.");
                    return false;
                }
            } catch (RinggzException e) {
                return false;
            }
        }
    }

    private void handleMessage(String message) {
        String[] messageparts = message.split(Protocol.DELIMITER);
        this.tui.output(message);
        String feedback = null;
        String packetHeader = messageparts[0];
        if (Packets.CONNECT.equals(packetHeader)) {
            if (messageparts.length == 2 && messageparts[1].equals(Protocol.ACCEPT)) {
                // message in tui
                this.connected = true;
                feedback = this.tui
                        .tuiInput("Please input the preffered amount of player and type of player "
                                + "\n( " + Protocol.HUMAN_PLAYER + " for humanplayer"
                                + ")\n(Separated by a space...)");
                int amount = Integer.parseInt(feedback.split(" ")[0]);
                String playerType = feedback.split(" ")[1];
                if (amount < 5 || amount > 1) {
                    this.playerAmount = amount;
                } else {
                    tui.output("the number is invalid, please restart");
                    this.shutDown();
                }
                if (Protocol.HUMAN_PLAYER.equals(playerType)) {
                    this.playerType = Protocol.HUMAN_PLAYER;
                } else {
                    this.playerType = Protocol.COMPUTER_PLAYER;
                }
                this.sendMessage(Packets.GAME_REQUEST + Protocol.DELIMITER + this.playerAmount
                        + Protocol.DELIMITER + this.playerType);
            } else {
                feedback = this.tui.tuiInput(
                        "the server has denied your connection request\nPress 1 to reconnect");
                if (Integer.parseInt(feedback) == 1) {
                    while (true) {
                        try {
                            new LocalGameController(this.tui, this.username, this.address,
                                    this.port);
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
                ((ServerPlayer) this.players.get(currentplayer)).setMove(new Move(
                        Integer.parseInt(messageparts[1]), Integer.parseInt(messageparts[2]),
                        Integer.parseInt(messageparts[3]), messageparts[5]));
            } catch (NumberFormatException | IndexOutOfBoundsException e) {
            }
        } else if (Protocol.Packets.GAME_ENDED.equals(packetHeader)) {
            gameEnded = true;
            this.tui.output(message);
        } else {
            tui.output("unknown packet received");
        }
    }

    private void sendMove(Move move) {
        String message = Protocol.Packets.MOVE + Protocol.DELIMITER + move.getX()
                + Protocol.DELIMITER + move.getY() + Protocol.DELIMITER + move.getMoveType()
                + Protocol.DELIMITER + move.getColor();
        this.sendMessage(message);
    }

    private boolean gameEnded;
    private int currentplayer = 0;
    Boolean[] canmove;

    public void play() {
        Move currentMove;
        this.tui.setBoard(this.board);
        new Thread(tui).start();
        boolean succes = false;
        while (!this.gameEnded || !this.board.boardIsFull()
                || !Arrays.asList(canmove).stream().noneMatch(a -> a.booleanValue() == true)) {
            while (!succes) {
                try {
                    if (players.get(currentplayer).playerCheck(this.board)) {
                        currentMove = players.get(currentplayer).makeMove(this.board);
                        if (this.checkMove(currentMove)) {
                            if (players.get(currentplayer) instanceof HumanPlayer
                                    || players.get(currentplayer) instanceof ComputerPlayer) {
                                this.sendMove(currentMove);
                            }
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
            one.playerScore = one.getPrimaryColor().colorWonFields
                    + one.getSecondaryColor().colorWonFields;
            two.playerScore = two.getPrimaryColor().colorWonFields
                    + two.getSecondaryColor().colorWonFields;
            if (one.playerScore > two.playerScore) {
                winner = one;
            } else if (two.playerScore > one.playerScore) {
                winner = two;
            } else if (one.playerScore == two.playerScore) {
                this.tui.output("It's a tie!");
            }
            this.tui.output("The winner of the match is " + winner.getName());
        } else if (colorwin == null) {
            this.tui.output("It is a tie....");
        } else {
            for (Player possiblewinner : this.players) {
                if (possiblewinner.getPrimaryColor() == colorwin) {
                    winner = possiblewinner;
                    break;
                }
            }
            this.tui.output("The winner of the match is " + winner.getName());
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
