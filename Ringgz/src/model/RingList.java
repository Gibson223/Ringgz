package model;

import java.util.LinkedList;
import java.util.List;

public class RingList {
	public List<Ring>  availableRings= new LinkedList<>();
	public RingList(){
		for (Color c: Color.values()) {
			for (int i = 0; i < 3; i++) {
				for (Tier tier: Tier.values()) {
				availableRings.add(new Ring(c, tier));
				}
			}
		}
	}
	public static void main(String[] args) {
		RingList a = new RingList();
		a.availableRings.stream().forEach(b -> System.out.println(" " + b.getColor() + b.getTier()));
	}
}
//		if (players == 2){
//			for (int number = 1; number <=24; number ++) {
//				availableRings.add(new Ring(Color.BLUE));
//			}
//			//bases
//			for(int t = 1; t <= 3; t++) {
//				Color c1 = Color.BLUE;
//				for (int i = 0; i <= 3; i++) {
//				availableRings.add(new Ring(c1, Tier.BASE));
//			}
//			c1.next();
//			}
//		}