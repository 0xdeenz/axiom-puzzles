pragma circom 2.1.4;
include "circomlib/comparators.circom";
include "circomlib/gates.circom";

// log2_ceil function borrowed from zk-email repo:
// https://github.com/zkemail/zk-email-verify/blob/main/circuits/helpers/utils.circom
function log2_ceil(a) {
    var n = a+1;
    var r = 0;
    while (n>0) {
        r++;
        n \= 2;
    }
    return r;
}


function build_mesh(mesh, n, bits, arr, match, set) {
    var len = n;
    var match_cnt = 0;
    var null = 0;
    for (var j = 0; j < len; j++) {
        if (arr[j][0] == match) {
            mesh[j][0][0] = null + 1 + j;
            mesh[j][1][0] = arr[j][1];
            mesh[j][2][0] = j - match_cnt;
            match_cnt++;
        }
        else {
            mesh[j][2][0] = -1;
            mesh[j][1][0] = 0;
            mesh[j][0][0] = null;
        }
    }
    for (var i = 1; i < bits + 1; i++) {
        var pow2 = 1;
        var k = 0;
        while (k < i - 1) {
            pow2 *= 2;
            k++;
        }
        for (var j = 0; j < pow2; j++){
            mesh[j][0][i] = mesh[j][0][i - 1];
            mesh[j][1][i] = mesh[j][1][i - 1];
            mesh[j][2][i] = mesh[j][2][i - 1];
            set[j][i - 1] = 1;
        }
        for (var j = pow2; j < len; j++) {
            if(mesh[j][0][i - 1] != null && ((mesh[j][2][i - 1] & pow2) > 0)) {
                mesh[j - pow2][0][i] = mesh[j][0][i - 1];
                mesh[j - pow2][1][i] = mesh[j][1][i - 1];
                mesh[j - pow2][2][i] = mesh[j][2][i - 1] - pow2;
                mesh[j][0][i] = null;
                mesh[j][1][i] = 0;
                mesh[j][2][i] = -1;
                set[j][i - 1] = 1;
                set[j - pow2][i - 1] = 1;
                mesh[j][3][i - 1] = 1;
            }
            else {
                if(!set[j - pow2][i - 1]) {
                    mesh[j - pow2][0][i] = mesh[j - pow2][0][i - 1];
                    mesh[j - pow2][1][i] = mesh[j - pow2][1][i - 1];
                    mesh[j - pow2][2][i] = mesh[j - pow2][2][i - 1];
                    set[j - pow2][i - 1] = 1;
                }
                mesh[j][0][i] = mesh[j][0][i - 1];
                mesh[j][1][i] = mesh[j][1][i - 1];
                mesh[j][2][i] = mesh[j][2][i - 1];
                set[j][i - 1] = 1;
            }
        }

    }
    for (var i = 1; i < bits + 1; i++) {
        var pow2 = 1;
        var k = 0;
        while (k < i - 1) {
            pow2 *= 2;
            k++;
        }
        for (var j = pow2; j < len; j++) {
            if(mesh[j][0][i - 1] == null && mesh[j - pow2][0][i] == null) {
                mesh[j][3][i - 1] = 1;
            }
        }

    }
    return mesh;
}

template VerifyMesh(n) {
    var bits = log2_ceil(n);
    signal input mesh[n][bits + 1];
    signal input in[n];
    signal input match_thing;
    signal input num_matches;
    signal input b;
    signal output out[n][2];
    signal input null;
    signal input claimed_swaps[n][bits];
    signal is_null_mesh[n][bits];
    signal match[n][bits][2];
    signal step1[n][bits];
    signal step2[n][bits];
    signal step0[n][bits];
    for (var i = 0; i < n; i++){
        in[i] === mesh[i][0];
    }
    for (var i = 0; i < bits; i++){
        var pow2 = 1;
        var k = 0;
        while (k < i) {
            pow2 *= 2;
            k++;
        }
        for (var j = 0; j < pow2; j++) {
            is_null_mesh[j][i] <== mesh[j][i];
            match[j][i][0] <== mesh[j][i + 1] - mesh[j][i];
            match[j][i][0] *  is_null_mesh[j][i] === 0;
            claimed_swaps[j][i] === 0;
        }
        for (var j = pow2; j < n; j++){
            is_null_mesh[j][i] <== mesh[j][i];
            match[j][i][0] <== mesh[j][i + 1] - mesh[j][i];
            // match[j][i][1] <== IsEqual()([mesh[j - pow2][i + 1], mesh[j][i]]);
            match[j][i][1] <== mesh[j - pow2][i + 1] - mesh[j][i];
            claimed_swaps[j][i] * match[j][i][1] === 0;
            step0[j][i] <== match[j][i][1] * match[j][i][0];
            step0[j][i] * is_null_mesh[j][i] === 0;
            step1[j][i] <== claimed_swaps[j][i] - claimed_swaps[j][i] * claimed_swaps[j - pow2][i];
            step2[j][i] <== step1[j][i] * is_null_mesh[j - pow2][i];
            step2[j][i] === 0;
            // * is_null_mesh[j - pow2][i]
        }
    }
    signal is_null[n];
    signal is_not_null[n];
    signal is_valid[n]; 
    signal greater_than_match[n + 1];
    greater_than_match[0] <== 0;
    signal eq_match[n];
    for (var i = 0; i < n; i++) {
        eq_match[i] <== IsEqual()([i, num_matches]);
        greater_than_match[i + 1] <== greater_than_match[i] + eq_match[i];
    }
    for (var i = 0; i < n; i++){
        is_null[i] <== IsEqual()([null, mesh[i][bits]]);
        is_not_null[i] <== 1 - is_null[i];
        is_null[i] === greater_than_match[i + 1];
        out[i][0] <== is_not_null[i] * match_thing;
        out[i][1] <== is_not_null[i] * (mesh[i][bits] - b);
    }
}

template Filter(n) {
    signal input in[n][2];
    signal input match; 
    signal output num_match;
    signal output out[n][2];
    signal num_matches[n + 1];
    signal does_match[n];
    component verify_mesh;
    num_matches[0] <== 0;
    var _match = match;
    var arr[n][2];
    for (var i = 0; i < n; i++){
        arr[i][0] = in[i][0];
        arr[i][1] = in[i][1];
    }
    signal newin[n];
    var nullval = 0;
    signal null <== nullval;
    var based;
    for (var i = 0; i <= n; i++) {
        var passes = 1;
        for (var j = 0; j < n; j++) {
            if(i + arr[j][1] == nullval){
                passes = 0;
            }
        }
        if (passes) {
            based = i;
        }
    }
    signal b <-- based;
    signal intermediate[n];
    signal prefixprod[n + 1];
    prefixprod[0] <== 1;
    signal is_zero[n];
    for (var i = 1; i < n + 1; i++){
        does_match[i - 1] <== IsEqual()([in[i - 1][0], match]);
        intermediate[i - 1] <== (in[i - 1][1] + b);
        prefixprod[i] <== prefixprod[i - 1] * intermediate[i - 1]; 
        num_matches[i] <== num_matches[i - 1] + does_match[i - 1];
        newin[i - 1] <== does_match[i - 1] * intermediate[i - 1];
    }
    signal badb <== IsZero()(prefixprod[n]);
    badb === 0;
    num_match <== num_matches[n];
    var bits = log2_ceil(n);
    var set[n][bits];
    for(var i; i < n; i++){
        for(var j; j < bits; j++){
            set[i][j] = 0;
        }
    }
    var claimed_swaps[n][bits];
    var new_mesh[n][4][bits + 1];
    var newer_mesh[n][bits + 1];
    new_mesh = build_mesh(new_mesh, n, bits, arr, _match, set);
    for (var i= 0; i < n; i++) {
        for (var j = 0; j < bits + 1; j++) {
            if (new_mesh[i][0][j] != 0){
                newer_mesh[i][j] = new_mesh[i][1][j] + based;
            }
            else {
                newer_mesh[i][j] = 0;
            }
        }
    }
    for (var i= 0; i < n; i++) {
        for (var j = 0; j < bits; j++) {
            claimed_swaps[i][j] = new_mesh[i][3][j];
        }
    }
    verify_mesh = VerifyMesh(n);
    verify_mesh.claimed_swaps <-- claimed_swaps;
    verify_mesh.mesh <-- newer_mesh;
    verify_mesh.in <== newin;
    verify_mesh.match_thing <== match;
    verify_mesh.num_matches <== num_matches[n];
    verify_mesh.b <== b;
    verify_mesh.null <== null;
    out <== verify_mesh.out;
}

component main = Filter(100);

/* INPUT = {
    "in": [["5", "94"], ["0", "42"], ["0", "93"], ["10", "57"], ["9", "18"], ["3", "11"], ["8", "28"], ["4", "47"], ["4", "72"], ["4", "66"], ["9", "12"], ["10", "9"], ["2", "49"], ["6", "3"], ["4", "78"], ["9", "44"], ["1", "5"], ["4", "75"], ["8", "66"], ["1", "53"], ["8", "22"], ["5", "45"], ["2", "10"], ["2", "18"], ["4", "33"], ["10", "72"], ["7", "61"], ["6", "32"], ["10", "44"], ["7", "32"], ["5", "13"], ["3", "46"], ["6", "25"], ["5", "91"], ["7", "38"], ["8", "36"], ["4", "91"], ["10", "36"], ["1", "16"], ["10", "77"], ["1", "82"], ["1", "98"], ["6", "63"], ["5", "17"], ["0", "23"], ["0", "63"], ["2", "33"], ["10", "57"], ["5", "25"], ["0", "73"], ["7", "82"], ["6", "91"], ["10", "33"], ["0", "94"], ["2", "8"], ["8", "40"], ["6", "68"], ["10", "18"], ["10", "99"], ["6", "45"], ["1", "91"], ["5", "28"], ["10", "20"], ["10", "40"], ["5", "42"], ["6", "91"], ["8", "7"], ["9", "66"], ["10", "78"], ["4", "61"], ["2", "97"], ["0", "81"], ["9", "2"], ["5", "12"], ["3", "72"], ["1", "53"], ["5", "46"], ["2", "89"], ["8", "22"], ["1", "92"], ["2", "48"], ["4", "57"], ["1", "3"], ["4", "55"], ["7", "78"], ["0", "21"], ["9", "48"], ["10", "64"], ["0", "6"], ["0", "58"], ["9", "10"], ["0", "71"], ["3", "77"], ["6", "12"], ["9", "86"], ["10", "8"], ["4", "10"], ["4", "95"], ["9", "46"], ["10", "62"]],
    "match": "0"
} */