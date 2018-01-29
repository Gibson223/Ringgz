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
    public static void main(String[] args) throws IOException {
		Client client = new Client();
		Thread c = new Thread(client);
		c.start();
	}
	public void run() {
		try {
			this.sendmessage();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		while (true) {
			//waiting
		}
	}
	public Client() throws IOException {
		ip = InetAddress.getLocalHost();
//		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		socket = new Socket(ip, PORT);
		this.dis = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"));
		this.dos = new PrintWriter(socket.getOutputStream(), true);
		String s = "you are connected to a clienthandler";
		dos.println(s);
	}
	public synchronized void readmessage() throws IOException {
		System.out.println(dis.readLine());
		System.out.println(dis.readLine());
		System.out.println("message read...");
		none = false;
	}
	public synchronized void sendmessage() throws IOException {
		dos.write("I hope it works");
	}
	public void stop() throws IOException {
		System.out.println("input received...\nShutting down...");
		dis.close();
		dos.close();
	}
}
