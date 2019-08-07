objConstructors = {'backends.get' : {'constructor' : 'LoadBalancedBackendc',
                                     'type' : 'LoadBalancedBackendi',
                                     'fields' : ['nic', 'mac', 'ip']}}
typeConstructors = {'ip_addrc' : 'ip_addri',
                    'LoadBalancedFlowc' : 'LoadBalancedFlowi'}
stateObjects = {'flow_emap' : emap,
                'flow_id_to_backend_id' : vector,
                'backends' : vector,
                'backend_ip_emap' : emap,
                'cht' : None}
