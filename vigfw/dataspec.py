objConstructors = {'flow_emap.get_key' : {'constructor' : 'FlowIdc',
                                          'type' : 'FlowIdi',
                                          'fields' : ['sp', 'dp', 'sip',
                                                      'dip', 'prot']}}
typeConstructors = {'FlowIdc' : 'FlowIdi',
                    'emap' : 'emap<FlowIdi>'}
stateObjects = {'flow_emap' : emap,
                'int_devices' : vector}
