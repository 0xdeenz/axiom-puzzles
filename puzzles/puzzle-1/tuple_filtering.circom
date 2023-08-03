pragma circom 2.0.0;

include "circomlib/comparators.circom";

// Inputs:
// * in is a fixed length array of 100 tuples
// * match is a arbitrary input value
// Outputs:
// * num_match is the number of elements of in whose first entry
//   matches match
// * the first num_match entries of out are the tuples in in
//   whose first entry agrees with match.  the remaining entries
//   in out are 0-padded.
template Filter(num_tuples) {
    signal input in[num_tuples][2];
    signal input match;
    signal output num_match;
    signal output out[num_tuples][2];
   
    // Used to compare the first entries in `in` that match with the value `match`
    component comparators[num_tuples];
    // Acts as a counter increasing by one each time the first entry in `in` equals `match`
    var _num_match = 0;

    for (var i = 0; i < num_tuples; i++) {
        // We check for equality via circomlib's `IsEqual` template
        comparators[i] = IsEqual();

        comparators[i].in[0] <== match;
        comparators[i].in[1] <== in[i][0];

        // The result of the template, `comparators[i].out`, will equal one only if the values match
        _num_match += comparators[i].out;
    }

    // Assign the output signal: number of elements of `in` whose first entry matches `match`
    num_match <== _num_match;

    // We will use this component to select the ith tuple on `in` whose first element equals `match`
    component count_matcher[num_tuples][num_tuples];
    // We will use these signals to asign values to each tuple on `out`
    signal first_value[num_tuples];
    signal second_value_sum_items[num_tuples][num_tuples];

    for (var i = 0; i < num_tuples; i++) {
        // Assigning the first item on the ith tuple of `out` -- we do still have to constrain it!
        first_value[i] <-- (i < _num_match) ? 1 : 0;
    }

    for (var i = 0; i < num_tuples; i++) {
        // Constraining the first value of the tuple to be either the given `match` or zero
        out[i][0] <== first_value[i] * match;
        out[i][0] * (out[i][0] - match) === 0;
        
        // Variable counting the number of tuples on `in` whose first value equals `match` 
        var count = 0;

        for (var j = 0; j < num_tuples; j++) {
            // Adding one to the count if the first value of the jth element of `in` equals `match`
            count += comparators[j].out;

            // We will only select the ith tuple of `in` whose first value equals `match`
            count_matcher[i][j] = IsEqual();

            count_matcher[i][j].in[0] <== (i + 1);
            count_matcher[i][j].in[1] <== count * comparators[j].out;

            second_value_sum_items[i][j] <== count_matcher[i][j].out * in[j][1];
        }

        // Will collect in a sum the second value on the ith tuple of `out`, which equals the ith tuple of `in` 
        // whose first item equals `match` -- the rest of the values on `_second_value_sum_items` are zero
        var _second_value_sum = 0;

        for (var j = 0; j < num_tuples; j++) {
            _second_value_sum += second_value_sum_items[i][j];
        }

        // Setting and constraining the second value of the tuple
        out[i][1] <== _second_value_sum;
    }
}

component main = Filter(100);

/* INPUT = {
    "in": [
        ["0", "2"], ["1", "1"], ["4", "1"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "1"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "3"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "4"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "1"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "1"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "5"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "1"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "2"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"],
        ["0", "2"], ["1", "1"], ["4", "1"], ["1", "1"], ["1", "1"], ["1", "1"], ["3", "1"], ["1", "1"], ["3", "2"], ["0", "5"]
    ],
    "match": "4"
} */

/* STATS: 

template instances: 3
non-linear constraints: 40400
linear constraints: 0
public inputs: 0
public outputs: 201
private inputs: 201
private outputs: 0
wires: 40602
labels: 71103
*/
