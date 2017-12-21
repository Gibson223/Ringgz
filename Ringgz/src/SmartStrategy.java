

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class SmartStrategy implements Strategy{

	@Override
	public String getName() {
		return "Smart";
	}

	@Override
	public int determineMove(Board b, Mark m) {
		List<Integer> emptyList = new ArrayList<>();
		for (int i = 0; i < 9; i++) {
			if (b.isEmptyField(i)) {
				emptyList.add(i);
			}
		}
		if (emptyList.contains(4)) {
			return 4;
		} else {
			for (int j : emptyList) {
				Board copy = b.deepCopy();
				copy.setField(j, m);
				if (copy.isWinner(m)) {
					return j;
				}
			}
			for (int k : emptyList) {
				Board copy = b.deepCopy();
				if (m == Mark.OO) {
					copy.setField(k, Mark.XX);
					if (copy.isWinner(Mark.XX)) {
						return k;
					}
				} else {
					copy.setField(k,Mark.OO);
					if (copy.isWinner(Mark.OO)) {
						return k;
					}
				}
			}
		
			Collections.shuffle(emptyList);
			return emptyList.get(0);			
		}
	}
}


