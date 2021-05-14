# nestelp
Count world views of epistemic logic programs on tree decompositions using databases.

## Requirements

### htd

[htd on github](https://github.com/TU-Wien-DBAI/htd/)

Branch `normalize_cli` is required by nestelp (currently not included in htd's master)

### Database
[PostgreSQL](https://www.postgresql.org)

### clingo and eclingo
[clingo](https://github.com/potassco/clingo)

[eclingo](https://github.com/potassco/eclingo)

### Python
* Python 3
* psycopg2
* future-fstrings (for compatibility with older versions)
```
pip install -r requirements.txt
```

## Configuration
Basic configuration (database connection, htd path, thresholds, ...) are configured in **config.json**

## Usage
```
$ python nesthdb.py --help
usage: nesthdb.py [general options] -f input-file problem-type [problem specific-options]

optional arguments:
  -h, --help            show this help message and exit
  -f FILE, --file FILE  Input file for the problem to solve (default: None)
  --no-cache            Disable cache (default: False)

general options:
  General options

  -t TYPE               type of the cluster run (default: )
  --runid RUNID         runid of the cluster run (default: 0)
  --config CONFIG       Config file (default: config.json)
  --log-level {DEBUG_SQL,DEBUG,INFO,WARNING,ERROR,CRITICAL}
                        Log level (default: INFO)
  --td-file TD_FILE     Store TreeDecomposition file (htd Output) (default:
                        None)
  --gr-file GR_FILE     Store Graph file (htd Input) (default: None)
  --faster              Store less information in database (default: False)
  --parallel-setup      Perform setup in parallel (default: False)

problem types:
  Type of problems that can be solved
  nesthdb.py problem-type --help for additional information on each type and problem specific options

  problem-type          Type of the problem to solve
    NestElp (nestelp)   Solve nested ELP instances
```

### Nestelp specific options
* without any option nestelp perform the world view existence problem
* `--count`: count the number of world views
* `--qr FILE`: given a space-seperated file of epistemic literals, perform quantitative reasoning over the given set