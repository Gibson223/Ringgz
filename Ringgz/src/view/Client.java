package view;

import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Scanner;

public class Client {

	public static void main(String[] args) {
		System.out.println("please type in a ");
		Scanner in = new Scanner(System.in);
		String name = in.nextLine().split(" ")[0];
        try {
			InetAddress addr = InetAddress.getByName(in.nextLine().split(" ")[1]);
		} catch (UnknownHostException e) {
			System.out.println("wrong adress");
			e.printStackTrace();
		}
        int port = Integer.parseInt(in.nextLine().split(" ")[2]);
		;
		Socket client = new Socket();
	}

}
