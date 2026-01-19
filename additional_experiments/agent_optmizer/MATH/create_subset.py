import os 
import json 
import random 

IN_DIR = 'MATH/dataset'
OUT_DIR = 'MATH/subset'

def process_dir(indir, outdir):
    # https://proceedings.mlr.press/v235/zhang24cd.html
    # For each data type (7 in total), we randomly 
    # choose 20 test examples and 80 training examples, 
    # and report the accuracy of each data type respectively.

    # However, the arXiv paper says the reverse, and Table 1
    # accuracies only make sense if train is 20 examples.

    sample_size = 20 if 'train' in indir else 80
    for filename in os.listdir(indir):
        tmp_path = os.path.join(indir, filename) 
        if os.path.isfile(tmp_path):
            if not filename.endswith('.jsonl'):
                continue 

            with open(tmp_path, 'r') as f:
                tmp = f.read().split('\n')
                #print(tmp)
                read_data = [x.strip() for x in tmp if x.strip() != '']
                save_data = random.sample(read_data, k=sample_size)
                #print(save_data)
                save_data = '\n'.join(save_data)
            with open(os.path.join(outdir, filename), 'w') as outfile:
                print(save_data, file=outfile, end='')
        else:
            os.makedirs(os.path.join(outdir, filename), exist_ok=True)
            process_dir(indir=os.path.join(indir, filename), 
                        outdir=os.path.join(outdir, filename))

if __name__ == '__main__':
    process_dir(IN_DIR, OUT_DIR) 