OPENQASM 2.0;
include "qelib1.inc";
qreg q[14];
creg c[14];
cx q[11],q[10];
cx q[9],q[8];
h q[5];
cx q[9],q[5];
t q[11];
tdg q[10];
cx q[11],q[10];
t q[9];
tdg q[5];
cx q[9],q[5];
z q[10];
cx q[11],q[10];
swap q[5],q[6];
cx q[2],q[3];
cx q[5],q[4];
sdg q[3];
cx q[2],q[3];
tdg q[8];
cx q[6],q[8];
t q[8];
cx q[9],q[8];
s q[6];
sdg q[8];
cx q[6],q[8];
h q[9];
t q[5];
cx q[9],q[5];
swap q[5],q[4];
tdg q[5];
cx q[9],q[5];
tdg q[4];
t q[5];
cx q[4],q[5];
swap q[4],q[10];
cx q[9],q[10];
s q[9];
z q[5];
cx q[9],q[5];
h q[10];
cx q[10],q[4];
cx q[10],q[11];
sdg q[5];
cx q[9],q[5];
tdg q[11];
cx q[10],q[11];
swap q[11],q[3];
t q[4];
cx q[3],q[4];
h q[3];
s q[2];
cx q[3],q[2];
s q[10];
sdg q[4];
cx q[10],q[4];
s q[11];
cx q[3],q[11];
t q[3];
tdg q[2];
cx q[3],q[2];
swap q[11],q[3];
tdg q[3];
cx q[2],q[3];
t q[3];
cx q[2],q[3];
cx q[11],q[3];
h q[11];
cx q[11],q[10];
cx q[10],q[4];
tdg q[10];
cx q[11],q[10];
t q[4];
cx q[10],q[4];
h q[10];
cx q[10],q[9];
cx q[9],q[5];
tdg q[9];
cx q[10],q[9];
t q[5];
cx q[9],q[5];
h q[9];
s q[8];
cx q[9],q[8];
swap q[5],q[9];
cx q[5],q[6];
t q[5];
tdg q[6];
cx q[5],q[6];
tdg q[8];
cx q[6],q[8];
t q[8];
cx q[6],q[8];
swap q[5],q[9];
cx q[9],q[8];
h q[9];
sdg q[5];
cx q[9],q[5];
s q[10];
cx q[9],q[10];
tdg q[10];
cx q[9],q[10];
swap q[5],q[9];
t q[9];
cx q[10],q[9];
s q[5];
sdg q[9];
cx q[5],q[9];
h q[10];
sdg q[4];
cx q[10],q[4];
s q[11];
cx q[10],q[11];
tdg q[11];
cx q[10],q[11];
swap q[11],q[3];
t q[4];
cx q[3],q[4];
h q[3];
cx q[3],q[2];
s q[10];
sdg q[4];
cx q[10],q[4];
cx q[3],q[11];
t q[3];
tdg q[2];
cx q[3],q[2];
swap q[12],q[2];
tdg q[11];
cx q[12],q[11];
t q[11];
cx q[12],q[11];
cx q[3],q[11];
h q[3];
cx q[3],q[4];
swap q[11],q[3];
cx q[11],q[10];
t q[11];
tdg q[10];
cx q[11],q[10];
tdg q[4];
cx q[10],q[4];
t q[4];
cx q[10],q[4];
h q[10];
cx q[10],q[9];
swap q[4],q[10];
cx q[11],q[10];
cx q[4],q[5];
t q[4];
tdg q[5];
cx q[4],q[5];
tdg q[9];
cx q[5],q[9];
t q[9];
cx q[5],q[9];
swap q[5],q[9];
cx q[4],q[5];
h q[9];
h q[6];
barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6],q[7],q[8],q[9],q[10],q[11],q[12],q[13];
measure q[3] -> c[0];
measure q[12] -> c[1];
measure q[10] -> c[2];
measure q[5] -> c[3];
measure q[8] -> c[4];
measure q[11] -> c[5];
measure q[4] -> c[6];
measure q[9] -> c[7];
measure q[6] -> c[8];
