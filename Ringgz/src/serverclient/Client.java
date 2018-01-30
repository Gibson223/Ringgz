package serverclient;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;

import sun.applet.Main;

public class Client implements Runnable{
	public static final int PORT = 23197;
	public static InetAddress ip;
	private Socket socket;
	private BufferedReader dis;
    private PrintWriter dos;
    boolean none = true;
    private String username;
    public static void main(String[] args) throws IOException {
		Client client = new Client("51IG");
		Thread c = new Thread(client);
		c.start();
	}
    public String INITmessage = "" + this.username ;
    
	public void run() {
		dos.write(INITmessage);
		while (true) {
			//waiting
		}
	}
	public Client(String username) throws IOException {
		this.username = username;
		ip = InetAddress.getLocalHost();
		socket = new Socket(ip, PORT);
		this.dis = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
		this.dos = new PrintWriter(socket.getOutputStream(), true);
	}
	public synchronized void readmessage() throws IOException {
		System.out.println(dis.readLine());
		System.out.println(dis.readLine());
		System.out.println("message read...");
	}
	public synchronized void sendmessage(String message) throws IOException {
		dos.write(message);
	}
	public void stop() throws IOException {
		System.out.println("Shutting down...");
		dis.close();
		dos.close();
	}
}
