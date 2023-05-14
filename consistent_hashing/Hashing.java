import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;

public class Hashing {    
    public static IntValue GetHashCode(StringValue input, StringValue key, IntValue min, IntValue max) {

        return IntValue.gen(CalculateHash(input, key, min.val, max.val));
    }

    private static int CalculateHash(StringValue input, StringValue key, int min, int max){
        int hash = key.hashCode() ^ input.hashCode(); // combine the key and input string hash codes
        int range = max - min + 1; // calculate the range of possible integer values
        hash = (hash & 0x7fffffff) % range; // ensure the hash is positive and within the range
        return hash + min; // add the minimum value to the hash to get the final result
    }
}