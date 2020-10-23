#!/bin/bash
# switch_var="--switch_check"
# icall_var="-i"
# taint0_var="-t --resolve_icall 0"
# taint1_var="-t"

for var in "--switch_check" "-i" "-t --resolve_icall 0" "-t"; do
    echo $var
    python3 /mnt/e/Ubuntu/work/dataflow/main.py -f /mnt/e/Ubuntu/work/binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 $var > /dev/null
done

# python3 /mnt/e/Ubuntu/work/dataflow/main.py -f /mnt/e/Ubuntu/work/binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 --switch_check > /dev/null
# python3 /mnt/e/Ubuntu/work/dataflow/main.py -f /mnt/e/Ubuntu/work/binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 -i > /dev/null
# python3 /mnt/e/Ubuntu/work/dataflow/main.py -f /mnt/e/Ubuntu/work/binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 -t --resolve_icall 0 > /dev/null
# python3 /mnt/e/Ubuntu/work/dataflow/main.py -f /mnt/e/Ubuntu/work/binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 -t > /dev/null
