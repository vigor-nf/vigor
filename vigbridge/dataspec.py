objConstructors = {'dyn_vals.get' : {'constructor' : 'DynamicValuec',
                                     'type' : 'DynamicValuei',
                                     'fields' : ['output_port']}}
typeConstructors = {'StaticKeyc' : 'StaticKeyi'}
stateObjects = {'dyn_emap' : emap,
                'dyn_vals' : vector,
                'stat_emap' : emap}
customPreamble = """
dchain stat_chain; //dummy
emap<StaticKeyi> stat_emap = emap(initial_st_map, initial_st_vec, stat_chain);
emap<StaticKeyi> final_stat_emap = emap(initial_st_map, initial_st_vec, stat_chain);
"""
