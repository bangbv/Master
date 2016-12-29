input_lines = LOAD '/tmp/cnn.txt.gz' AS (line:chararray);
input_lines2 = LOAD '/tmp/cnn.txt.gz' AS (line:chararray);

-- Extract words from each line and put them into a pig bag
-- datatype, then flatten the bag to get one word on each row
words = FOREACH input_lines GENERATE FLATTEN(TOKENIZE(line)) AS word;
words2 = FOREACH input_lines2 GENERATE FLATTEN(TOKENIZE(line)) AS word;

-- filter out any words that are just white spaces
filtered_words = FILTER words BY word MATCHES '\\w+';
filtered_words2 = FILTER words2 BY word MATCHES '\\w+';

-- create a group for each word
word_groups = GROUP filtered_words BY word;
word_groups2 = GROUP filtered_words2 BY word;

-- count the entries in each group
word_count = FOREACH word_groups GENERATE COUNT(filtered_words) AS count, group AS word;
joinR = JOIN word_groups BY SUBSTRING($0, 0, 1), word_groups2 BY SUBSTRING($0, 0, 1);
joinorder = ORDER joinR BY $0;
DUMP joinorder;

-- order the records by count
ordered_word_count = ORDER word_count BY count DESC;
DUMP ordered_word_count