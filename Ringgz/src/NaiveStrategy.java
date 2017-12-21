

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
public class NaiveStrategy implements Strategy {

	@Override
	public String getName() {
		return "Naive";
	}

	@Override
	public int determineMove(Board b, Mark m) {
		List<Integer> emptyList = new ArrayList<>();
		for (int i = 0; i < 9; i++) {
			if (b.isEmptyField(i)) {
				emptyList.add(i);
			}
		}
		Collections.shuffle(emptyList);
		return emptyList.get(0);
	}
}
