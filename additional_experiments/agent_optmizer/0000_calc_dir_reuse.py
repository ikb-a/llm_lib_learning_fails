from pathlib import Path
from collections import Counter
import json 
import re
from tabulate import tabulate

PATH_TEMPLATES = [
f"outputs_train/{ds}_" + suffix
for ds in ['precalculus', 'algebra', 'counting_and_probability', 'number_theory', 'geometry', ] for suffix in [ 'gpt4o_{}_10epochs']] # '{}',

PATTERN = re.compile(r"\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\+\s\{'name': '(.+?)'")

if __name__ == '__main__':
    global_table = []
    for template in PATH_TEMPLATES:
        for i in range(3):
            full_path = Path(template.format(i))

            if not full_path.exists():
                print(f'WARNING {full_path} does not exist.')
                continue 

            print('-'* 10)
            print(full_path)

            usage = Counter()

            with open(full_path/'results.jsonl', 'r') as infile:
                lines = [json.loads(x) for x in infile.readlines() if x.strip() != '']

            successes = set(x['index'] for x in lines if x['is_correct'])

            out = []
            for x in full_path.iterdir():
                if str(x).endswith('.out'):
                    out.append(x)
            if len(out) != 1:
                print(f'WARNING, wrong number of outfiles?:\n {out}')
                continue 

            out = out [0]

            with open(out) as infile:
                log = infile.read()

            log = log.split('BEGIN EVAL PROBLEM #')
            log = log[1:]
            log = {int(x.split()[0]): x for x in log}

            for index in successes:
                logfile = log[index]
                
                names = set(match.group(1) for match in re.finditer(PATTERN, logfile))
                usage.update(names)
                
            print(f'{len(successes)}/80 Successes')
            #print("REUSE STATISTICS")
            
            #print('\n'.join([str((x[0], x[1])) for x in usage.most_common()]))
            #print(tabulate(usage.most_common()))
            global_table += [(f'{"MATH geometry" if "geometry" in str(full_path) else "MATH Precalculus"} Run {i} ({len(successes)}/80 Successes)',)]
            global_table += [(r'\texttt{' +x[0] + r'}', x[1]) for x in usage.most_common()]
    print(tabulate(global_table, tablefmt='latex_raw'))
            

            
                


