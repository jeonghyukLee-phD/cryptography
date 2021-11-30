# FWSMAS
Experiment code for Forward secure multi-user aggregate signature scheme[1]. 

It utilizes TurboPlonk[2] as a building block for the zero-knowledge proof systems.

The algorithm has O(1) metric in Setup,Update,Sign,Verify and supports an aggregation of multi user signatures with different messages and time periods. 

[1] Lee, Jeonghyuk, Jihye Kim, and Hyunok Oh. "Forward-secure Multi-user Aggregate Signatures based on zk-SNARKs." IEEE Access 9 (2021): 97705-97717.

[2] Gabizon, Ariel, Zachary J. Williamson, and Oana Ciobotaru. "PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge." IACR Cryptol. ePrint Arch. 2019 (2019): 953.


