import os

THRESHOLD = 20000000000

lists = "/home/katsura/github.com/moratorium08/hopdr/hopdr/benchmark/lists"
inputs = "/home/katsura/github.com/moratorium08/hopdr/hopdr/benchmark/inputs"
results = "/home/katsura/github.com/moratorium08/hopdr/hopdr/results/checker"

lin = ("comp_LIA-lin", "lin-spacer-2023-12-31-01.csv", "lin-golem-2023-12-31-01.csv")
nonlin = ("comp_LIA-nonlin", "nonlin-spacer-2023-12-31-01.csv", "nonlin-golem-2023-12-31-01.csv")


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

    p = os.path.join(results, bench[1])
    spacer_data, spacer_keys = gen_dict(p)
    p = os.path.join(results, bench[2])
    golem_data, golem_keys = gen_dict(p)

    spacer_new_data = []
    golem_new_data = []

    result = []

    assert(set(instances) == set(spacer_keys))
    assert(set(instances) == set(golem_keys))
    keys = golem_keys

    for instance in keys:
        sp = spacer_data[instance]
        gl = golem_data[instance]
        if sp[2] == 'valid' or gl[2] == 'valid':
            continue

        size = get_size(instance)
        if size > THRESHOLD:
            continue
        result.append(instance)
        spacer_new_data.append(sp)
        golem_new_data.append(gl)

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
