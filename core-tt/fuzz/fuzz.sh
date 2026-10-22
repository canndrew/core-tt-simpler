#!/bin/sh

# Run cargo fuzz with a sane set of options.
#
# It would be better if these options could be set in a config file somewhere
# but I can find any way to do that.

cargo fuzz run core_tt_fuzz -- \
    #-max_len=256 \
    -max_len=64 \
    -timeout=30 \
    -rss_limit_mb=16384 \
    -fork=1 \
    -ignore_ooms=1 \

