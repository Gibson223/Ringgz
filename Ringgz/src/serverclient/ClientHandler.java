package serverclient;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.net.Socket;

public class ClientHandler implements Runnable{
	private BufferedReader dis;
	private BufferedWriter dos;
	private Server server;
	
    public final Socket s;
    public  String name;
     
 
    // Constructor
    public ClientHandler(Socket s) throws IOException 
    {
        this.s = s;
        this.dis = new BufferedReader(new InputStreamReader(s.getInputStream(), "UTF-8"));
		this.dos = new BufferedWriter(new OutputStreamWriter(s.getOutputStream(), "UTF-8"));
    }
	@Override
	public void run(){
		try {
			while(true) {
			String initmessage = this.dis.readLine();
			if (initmessage != null) {
				server.serverPrint(initmessage);
			}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		//todo splitter init message contains packettype, username
		
	}
	
}
