objConstructors = {'flow_emap.get_key' : {'constructor' : 'FlowIdc',
                                          'type' : 'FlowIdi',
                                          'fields' : ['sp', 'dp', 'sip', 'dip',
                                                      'idev', 'prot']}}
typeConstructors = {'FlowIdc' : 'FlowIdi',
                    'emap' : 'emap<FlowIdi>'}
stateObjects = {'flow_emap' : emap}
