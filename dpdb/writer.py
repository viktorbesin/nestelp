import math

def normalize_cnf(clauses, var=None, return_mapping=False):
    var_map={}
    rev_var_map={}
    num_vars = 0
    mapped_clauses = []
    mapped_vars = None
    for c in clauses:
        mapped_clause = []
        for v in c:
            if not abs(v) in var_map:
                num_vars += 1
                var_map[abs(v)] = num_vars
                rev_var_map[num_vars] = abs(v)
            mapped_clause.append(int(math.copysign(var_map[abs(v)],v)))
        mapped_clauses.append(mapped_clause)
    if var is not None:
        mapped_vars = set()
        for v in var:
            if not v in var_map:
                num_vars += 1
                var_map[v] = num_vars
                rev_var_map[num_vars] = v
            mapped_vars.add(var_map[v])
    if return_mapping == True:
        return mapped_clauses, mapped_vars,num_vars,var_map,rev_var_map
    else:
        return mapped_clauses, mapped_vars,num_vars

def denormalize_cnf(clauses,vars,proj_vars,mapping):
    mapped_clauses = []
    mapped_vars = set()
    mapped_proj_vars = set()
    for c in clauses:
        mapped_clause = []
        for v in c:
            mapped_clause.append(int(math.copysign(mapping[abs(v)],v)))
        mapped_clauses.append(mapped_clause)
    for v in vars:
        mapped_vars.add(mapping[v])
    for v in proj_vars:
        mapped_proj_vars.add(mapping[v])
    return mapped_clauses, mapped_vars, mapped_proj_vars

class Writer(object):
    def write(self, str):
        pass

    def writeline(self, str):
        self.write(str)
        self.write("\n")

    def flush(self):
        pass

    def write_gr(self, num_vertices, edges):
        self.writeline("p tw {0} {1}".format(num_vertices,len(edges)))
        for e in edges:
            self.writeline("{0} {1}".format(e[0],e[1]))
        self.flush()

    def write_td(self, num_bags, tree_width, num_orig_vertices, root, bags, edges):
        self.writeline("s td {0} {1} {2}".format(num_bags, tree_width + 1, num_orig_vertices))
        self.writeline("c r {0}".format(root))
        for b, v in bags.items():
            self.writeline("b {0} {1}".format(b, " ".join(map(str,v))))
        for e in edges:
            self.writeline("{0} {1}".format(e[0],e[1]))
        self.flush()

    def write_cnf(self, num_vars, clauses, normalize=False, proj_vars=None):
        if normalize:
            clauses,proj_vars,num_vars = normalize_cnf(clauses, proj_vars)
        self.writeline("p cnf {} {}".format(num_vars, len(clauses)))
        if proj_vars is not None:
            self.writeline("c ind {} 0".format(" ".join(map(str,proj_vars))))
        for c in clauses:
            self.writeline("{} 0".format(" ".join(map(str,c))))
        self.flush()

    def write_elp(self, elp):
        def _get_symbol_for_atom(atom, head=False):
            if abs(atom) not in elp.var_symbol_dict.keys():
                return f"x_{abs(atom)}" if atom > 0 else f"not x_{abs(atom)}"
            if atom < 0:
                _neg = "not"
            else:
                _neg = ""
            symbol = elp.var_symbol_dict[abs(atom)]

            # check if its still epistemic
            if symbol.startswith("aux_not_sn_"):
                if head:
                    return f"-{symbol[11:]}"
                return f"{_neg} &k{{~ -{symbol[11:]}}}" if len(elp.epistemic_atoms) > 0 else f"{_neg} -{symbol[11:]}"
            elif symbol.startswith("aux_sn_"):
                if head:
                    return f"-{symbol[7:]}"
                return f"{_neg} &k{{-{symbol[7:]}}}" if len(elp.epistemic_atoms) > 0 else f"{_neg} -{symbol[7:]}"
            elif symbol.startswith("aux_not_"):
                if head:
                    return f"{symbol[8:]}"
                return f"{_neg} &k{{~ {symbol[8:]}}}" if len(elp.epistemic_atoms) > 0 else f"{_neg} {symbol[8:]}"
            elif symbol.startswith("aux_"):
                if head:
                    return f"{symbol[4:]}"
                return f"{_neg} &k{{{symbol[4:]}}}" if len(elp.epistemic_atoms) > 0 else f"{_neg} {symbol[4:]}"

            return f"{_neg} {symbol}"

        str_rules = []

        for cr in elp.choice_rules:
            # str_rules.append(f"{{ {_get_symbol_for_atom(cr['head'][0])} }}.")
            self.writeline(f"{{ {_get_symbol_for_atom(cr['head'][0])} }}.")

        for r in elp.rules:
            if (r['body'] == []):
                # TODO: cancel earlier to save time
                if (len(r['head']) == 0):
                    # str_rules.append(f":- .")
                    self.writeline(f":- .")
                    continue
                if(len(r['head']) == 1):
                    # str_rules.append(f"{_get_symbol_for_atom(r['head'][0], True)}.")
                    self.writeline(f"{_get_symbol_for_atom(r['head'][0], True)}.")
                    continue
                # str_rules.append(f"{','.join([_get_symbol_for_atom(ha, True) for ha in r['head']])}.")
                self.writeline(f"{','.join([_get_symbol_for_atom(ha, True) for ha in r['head']])}.")
            else:
                # str_rules.append(f"{','.join([_get_symbol_for_atom(ha, True) for ha in r['head']])} :- "
                #        f"{','.join([_get_symbol_for_atom(ba) for ba in r['body']])}.")
                self.writeline(f"{','.join([_get_symbol_for_atom(ha, True) for ha in r['head']])} :- "
                       f"{','.join([_get_symbol_for_atom(ba) for ba in r['body']])}.")
        if elp.epistemic_constraints is not None:
            for pc in elp.epistemic_constraints['p']:
                # str_rules.append(f":- not &k{{{_get_symbol_for_atom(abs(pc), True)}}}.")
                self.writeline(f":- not &k{{{_get_symbol_for_atom(abs(pc), True)}}}.")
            for nc in elp.epistemic_constraints['n']:
                # str_rules.append(f":- not &k{{~{_get_symbol_for_atom(abs(nc), True)}}}.")
                self.writeline(f":- not &k{{~{_get_symbol_for_atom(abs(nc), True)}}}.")
            for uc in elp.epistemic_constraints['u']:
                symbol = _get_symbol_for_atom(abs(uc), True)
                # str_rules.append(f":- &k{{{symbol}}}.")
                # str_rules.append(f":- &k{{~{symbol}}}.")
                self.writeline(f":- &k{{{symbol}}}.")
                self.writeline(f":- &k{{~{symbol}}}.")

        # print ('\n'.join(str_rules))
        self.flush()

class StreamWriter(Writer):
    def __init__(self, stream):
        self.stream = stream

    def write(self, str):
        self.stream.write(str.encode())

    def flush(self):
        self.stream.flush()

class FileWriter(Writer):
    def __init__(self, fname, mode="w"):
        self.file_name = fname
        self.mode = mode
        if self.mode[-1] != "b":
            self.mode += "b"

    def __enter__(self):
        self.fd = open(self.file_name, self.mode)
        self.stream_writer = StreamWriter(self.fd)
        return self.stream_writer

    def __exit__(self, type, value, traceback):
        self.fd.close()

    def write(self, str):
        self.fd.write(str)

    def flush(self):
        self.stream_writer.flush()
