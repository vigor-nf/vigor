# DIR-24-8-BASIC

This is a formally verified DIR-24-8-BASIC implementation for the IPv4 addresses longest prefix match described by Pankaj Gupta, Steven Lin and Nick McKeown in their paper [Routing Lookups in Hardware at Memory Access Speeds](http://tiny-tera.stanford.edu/~nickm/papers/Infocom98_lookup.pdf).

## Assumptions
1. Static configuration : The tables must be filled once and for all before any lookup, for any modification of the routing please stop and reboot the router with the new rules.
2. Ascending prefixlength : The rules must be inserted from the lowest to the biggest prefixlengths.
