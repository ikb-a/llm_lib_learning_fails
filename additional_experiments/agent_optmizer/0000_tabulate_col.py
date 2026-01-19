#from tabulate import tabulate

import json 
import numpy as np 
from collections import defaultdict
from tabulate import tabulate

def std(x):
    return np.std(x,ddof=1)

def avg(x):
    return sum(x)/len(x)



def plot(datasets, models):
    assert len(datasets) == 1
    results = {} # Model, dataset, direct/train
    modes = ['train', 'direct']
    for (model, suffix) in models:
        results[model] = {}
        for dataset in datasets:
            results[model][dataset] = {}
            for mode in modes:
                results[model][dataset][mode] = defaultdict(lambda: '')

                if model == '4o' and dataset not in ['geometry', 'precalculus']:
                    continue

                # Get accuracy
                accs = []
                train_costs = []
                test_costs = []
                for i in range(3):
                    result_path = f'outputs_{mode}/{dataset}{suffix}_{i}/results.jsonl'
                    if model == '4o' and mode == 'train':
                        result_path = f'outputs_{mode}/{dataset}{suffix}_{i}_10epochs/results.jsonl'
                    with open(result_path) as f:
                        data = f.readlines()
                    data = [json.loads(x.strip()) for x in data if x.strip() != '']
                    assert len(data) == 80
                    correct = len([x for x in data if x['is_correct']])
                    accs.append(correct/len(data))

                    if mode == 'train':
                        cost_path = f'outputs_{mode}/{dataset}{suffix}_{i}/optimizer_total_cost.json'
                        if model == '4o' and mode == 'train':
                            cost_path = f'outputs_{mode}/{dataset}{suffix}_{i}_10epochs/optimizer_total_cost.json'
                        with open(cost_path) as f: 
                            data = json.load(f)
                        train_costs.append(data["total"]["total_cost"])

                    usage_path = f'outputs_{mode}/{dataset}{suffix}_{i}/test_time_total_usage.json'
                    if model == '4o' and mode == 'train':
                        usage_path = f'outputs_{mode}/{dataset}{suffix}_{i}_10epochs/test_time_total_usage.json'
                    with open(usage_path) as f: 
                        data = json.load(f)
                        test_costs.append(data["total_cost"])
                
                results[model][dataset][mode]['acc'] = f'${avg(accs)*100:.2f} \\pm {std(accs)*100:.2f}\\%$'
                if mode == 'train':
                    results[model][dataset][mode]['train'] = f'$\\${avg(train_costs):.2f} \\pm {std(train_costs):.2f}$'
                    assert len(train_costs) == len(test_costs)
                    sum_costs = [x+y for (x,y) in zip(train_costs, test_costs)]
                    results[model][dataset][mode]['sum'] = f'$\\${avg(sum_costs):.2f} \\pm {std(sum_costs):.2f}$'
                else:
                    results[model][dataset][mode]['train'] = '$\\$0$'
                    results[model][dataset][mode]['sum'] = f'$\\${avg(test_costs):.2f} \\pm {std(test_costs):.2f}$'
                results[model][dataset][mode]['test'] = f'$\\${avg(test_costs):.2f} \\pm {std(test_costs):.2f}$'


    DISP = {'number_theory': 'num.', 'counting_and_probability': 'count.', 'acc': 'Accuracy', 'train': 'Train', 'test': 'Inference', 'sum': 'Cost'}
    def disp(x):
        if x not in DISP:
            return x 
        return DISP[x]


    #print(json.dumps(results, indent=2))
    table = [[datasets[0]] + [f'{disp(y)}' for x in datasets for y in ['acc', 'train', 'test']]]


    for model, _ in models:
        for mode in modes:
            row = [f'{model} ({mode})'] + [f'{results[model][x][mode][y]}' for x in datasets for y in ['acc', 'train', 'test']]
            table.append(row)

    # Horizontal table
    #print(tabulate(table))

    table_ver = [[table[i][j] for i in range(len(table))] for j in range(len(table[0]))]
    #print(tabulate(table_ver))
    print()
    print(r'\begin{table}')
    print(tabulate(table_ver, tablefmt='latex_raw'))
    print(r'\caption{AgentOptimizer performance on MATH ' + f'{dataset.replace("_", " ")}' + r'. ``train' + "''" + r' indicates AgentOptimizer was used to train a library, ``direct' +"''" + r' indicates that the ReAct-like baseline was used directly without any library.}\label{app:agent_opt_'+ dataset +r'}')
    print(r'\end{table}')
    print()

if __name__ == '__main__':
    datasets = ['geometry', 'precalculus'] # 'precalc'
    models = [('4o-mini', ''), ('4o', '_gpt4o')]
    plot(['geometry'], models)
    plot(['precalculus'], models)
    #table = [[''] + [f'{x} ({y})' for x in datasets for y in ['acc', 'train', 'test']]] 

    plot(['algebra'], [('4o-mini', '')])

    plot(['counting_and_probability'], [('4o-mini', '')])

    plot(['number_theory'], [('4o-mini', '')])

