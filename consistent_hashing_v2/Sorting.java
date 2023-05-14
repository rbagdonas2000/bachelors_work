import tlc2.value.impl.*;
import java.util.*;
import java.io.*;

public class Sorting {
    
    public static TupleValue SortCustomRecords(Value s) {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq != null && seq.size() != 0)
        {
            int n = seq.size();
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n-i-1; j++) {
                    if (((RecordValue)seq.elems[j]).values[2] == BoolValue.ValTrue && ((RecordValue)seq.elems[j+1]).values[2] == BoolValue.ValFalse) {
                        RecordValue temp = (RecordValue)seq.elems[j];
                        seq.elems[j] = seq.elems[j+1];
                        seq.elems[j+1] = temp;
                    }
                }
            }
        }
        return new TupleValue(seq);
    }
}