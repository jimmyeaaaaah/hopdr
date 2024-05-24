import os

THRESHOLD = 20000000000

lists = "/home/katsura/github.com/moratorium08/hopdr/hopdr/benchmark/lists"
inputs = "/home/katsura/github.com/moratorium08/hopdr/hopdr/benchmark/inputs"
results = "/home/katsura/github.com/moratorium08/hopdr/hopdr/results/checker"

lin = ("comp_LIA-lin", ["lin-spacer-2023-12-31-01.csv", "lin-golem-2023-12-31-01.csv", "lin-eldarica-2024-05-18-17.csv", "lin-hoice-2024-05-17-00.csv"])
nonlin = ("comp_LIA-nonlin", ["nonlin-spacer-2023-12-31-01.csv", "nonlin-golem-2023-12-31-01.csv", "nonlin-eldarica-2024-05-18-17.json", "nonlin-hoice-2024-05-17-00.csv"])


def gen_dict(p):
    with open(p) as f:
        spacer_csv = f.read().strip().split("\n")

    spacer_data = dict()
    keys = []
    for l in spacer_csv:
        xs = l.split(", ")
        spacer_data[xs[0]] = xs
        keys.append(xs[0])
    return spacer_data, keys


def get_size(instance):
    with open(os.path.join(inputs, instance)) as f:
        return len(f.read())


def main(bench):
    p = os.path.join(lists, bench[0])
    with open(p) as f:
        instances = f.read().strip().split("\n")

    datas = []
    keys = []
    for filename in bench[1]:
        p = os.path.join(results, filename)
        d, k= gen_dict(p)
        datas.append(d)
        keys.append(k)

    
    new_datas = [[] for _ in datas]

    result = []

    #assert(set(instances) == set(spacer_keys))
    #assert(set(instances) == set(golem_keys))
    # use keys in bench[1][0]
    keys = keys[0]

    for instance in keys:
        if any(x[instance] == 'valid' for x in datas):
            continue

        size = get_size(instance)
        if size > THRESHOLD:
            continue
        result.append(instance)
        for idx, data in enumerate(datas):
            new_datas[idx].append(data[instance])

    p = os.path.join(lists, bench[0] + '-small')
    print(p, len(result))
    with open(p, "w") as f:
        f.write('\n'.join(result))

    p = os.path.join(lists, bench[1].replace('.csv', '') + '-small.csv')
    print(p)
    with open(p, "w") as f:
        for l in spacer_new_data:
            f.write(', '.join(l) + '\n')

    p = os.path.join(lists, bench[2].replace('.csv', '') + '-small.csv')
    print(p)
    with open(p, "w") as f:
        for l in golem_new_data:
            f.write(', '.join(l) + '\n')


main(lin)
main(nonlin)

