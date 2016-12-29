L0 = LOAD '/tmp/omniturelogs/Omniture.0.tsv.gz' USING PigStorage();
L1 = LOAD '/tmp/omniturelogs/Omniture.1.tsv.gz' USING PigStorage();
L2 = LOAD '/tmp/omniturelogs/Omniture.2.tsv.gz' USING PigStorage();
L3 = LOAD '/tmp/omniturelogs/Omniture.3.tsv.gz' USING PigStorage();
L4 = LOAD '/tmp/omniturelogs/Omniture.4.tsv.gz' USING PigStorage();
L5 = LOAD '/tmp/omniturelogs/Omniture.5.tsv.gz' USING PigStorage();
LOG = UNION L0, L1, L2, L3, L4, L5; 
STORE LOG INTO '/tmp/pigOutput' USING PigStorage();