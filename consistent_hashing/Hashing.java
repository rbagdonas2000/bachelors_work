import tlc2.value.impl.*;
import java.util.*;
import tlc2.module.*;

public class Hashing {
    public static IntValue GetHashCode(StringValue input, StringValue key, IntValue min, IntValue max) {
        int hash = key.hashCode() ^ input.hashCode(); // combine the key and input string hash codes
        IntValue range = Integers.Plus(Integers.Minus(max, min), IntValue.gen(1)); // calculate the range of possible integer values
        IntValue newHash = Integers.Mod(IntValue.gen(hash & 0x7fffffff), range); // ensure the hash is positive and within the range
        return Integers.Plus(newHash, min);
    }
}