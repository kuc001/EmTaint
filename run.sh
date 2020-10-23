#!/bin/bash

main_file="/mnt/e/Ubuntu/work/dataflow/main.py"
binary_path="/mnt/e/Ubuntu/work/binaries/"

function analyze_binary(){
    for var in "--switch_check" "-i" "-t --resolve_icall 0" "-t"; do
        echo $1 $2 $3 $var
        python3 $main_file -f $binary_path$1 -n $2 -v $3 $var > /dev/null 2>&1
    done
}

# analyze_binary "rv130_v44/httpd" "rv130" "1_0_3_44"

# analyze_binary "rv320_v4_4_20/ssi.cgi" "rv320" "v4_4_20"

# analyze_binary "RV16X_26X-v1.0.00.17/admin.cgi" "RV160" "v1.0.00.17"

# analyze_binary "tew827_v204/ssi" "tew827" "v204"

# analyze_binary "tew632_vB32/httpd" "tew632" "vB32"

# analyze_binary "DIR-645-v1.03/cgibin" "dir645" "v1.03"

# analyze_binary "DIR868LA1_FW112b04/cgibin" "DIR868LA1" "FW112b04"

# analyze_binary "DIR652B1_FW200B40/ssi" "DIR652B1" "FW200B40"

# analyze_binary "dir825_v210/httpd" "dir825" "vB210"

# analyze_binary "DIR-890L-v1.03/cgibin" "dir890L" "v1.03"

# analyze_binary "DIR823GA1_FW102B03/goahead" "DIR823GA1" "FW102B03"

# analyze_binary "DCS-5020L_A1_v1.15.12/alphapd" "DCS-5020L" "A1_v1.15.12"

# analyze_binary "DAP-1860_A1_103B03/uhttpd" "DAP-1860" "A1_103B03"

# analyze_binary "DGN1000-v1.1.00.46/setup.cgi" "DGN1000" "v1_1_00_46"

# analyze_binary "DGN2200-v1.0.0.50/httpd" "DGN2200" "v1_0_0_50"

analyze_binary "AC1450-v1.0.0.36/httpd" "AC1450" "v1_0_0_36"

# analyze_binary "R6200v2-v1.0.3.12/httpd" "R6200v2" "v1_0_3_12"

# analyze_binary "R6300v2-v1.0.4.18/httpd" "R6300v2" "v1_0_4_18"

# analyze_binary "R6400v2-v1.0.2.46/httpd" "R6400" "v1_0_2_46"

# analyze_binary "R6700-v1.0.1.36/httpd" "R6700" "v1_0_1_36"

# analyze_binary "R7000P-v1.3.0.8/httpd" "R7000P" "v1_3_0_8"

# analyze_binary "R7300-v1.0.0.56/httpd" "R7300" "v1_0_0_56"

# analyze_binary "R7500v2-v1.0.3.16/net-cgi" "R7500v2" "v1_0_3_16"

# ****** R7800 series *******
# analyze_binary "R7800-v1.0.2.32/net-cgi" "R7800" "v1_0_2_32"
# analyze_binary "R7800-V1.0.2.36/net-cgi" "R7800" "V1.0.2.36"
# analyze_binary "R7800-V1.0.2.40/net-cgi" "R7800" "V1.0.2.40"
# analyze_binary "R7800-V1.0.2.52/net-cgi" "R7800" "V1.0.2.52"
# analyze_binary "R7800-V1.0.2.58/net-cgi" "R7800" "V1.0.2.58"
# analyze_binary "R7800-V1.0.2.60/net-cgi" "R7800" "V1.0.2.60"
# analyze_binary "R7800-v1.0.2.62/net-cgi" "R7800" "v1.0.2.62"
# analyze_binary "R7800-v1.0.2.68/net-cgi" "R7800" "v1.0.2.68"

# analyze_binary "R7900-v1.0.1.26/httpd" "R7900" "v1_0_1_26"

# analyze_binary "R8000-v1.0.4.4/httpd" "R8000" "v1_0_4_4"

# analyze_binary "R8300-v1.0.2.106/httpd" "R8300" "v1_0_2_106"

# analyze_binary "R8500-v1.0.2.106/httpd" "R8500" "v1_0_2_106"

# analyze_binary "R8900-v1.0.2.40/net-cgi" "R8900" "v1_0_2_40"

# analyze_binary "R9000-v1.0.2.40/net-cgi" "R9000" "v1_0_2_40"

analyze_binary "WNR3500Lv2-v1.2.0.46/httpd" "WNR3500Lv2" "v1_2_0_46"

analyze_binary "XR500-v2.1.0.4/net-cgi" "XR500" "v2_1_0_4"

# analyze_binary "NC260_1.5.2/ipcamera" "NC260" "v1_5_2"

# analyze_binary "US_AC9V1.0BR_V15.03.05.14/app_data_center" "US_AC9V1.0BR_V15" "V15.03.05.14"

# analyze_binary "US_AC9V1.0BR_V15.03.05.14/httpd" "US_AC9V1.0BR_httpd" "V15.03.05.14"

# analyze_binary "US_AC9V3.0RTL_V15.03.06.42/httpd" "US_AC9V3.0RTL" "V15.03.06.42"

# analyze_binary "US_AC10V1.0RTL_V15.03.06.23/httpd" "US_AC10V1.0RTL" "V15.03.06.23"

# analyze_binary "US_AC15V1.0BR-v15.03.05.18/app_data_center" "US_AC15V1.0BR" "v15.03.05.18"

# analyze_binary "US_WH450AV1BR_WH450A_V1.0.0.18/httpd" "US_WH450AV1BR" "V1.0.0.18"

# analyze_binary "US_AC15V1.0BR-v15.03.05.18/nginx" "US_AC15V1.0BR-nginx" "v15.03.05.18"

# analyze_binary "wr1043ndv3_en_3_16_9/httpd" "wr1043ndv3" "en_3_16_9"

# analyze_binary "wr940nv4_us_3_16_9/httpd" "wr940nv4" "us_3_16_9"

# analyze_binary "mr3020nv1_en_3_17_2/httpd" "mr3020nv1" "en_3_17_2"

# analyze_binary "FH1201/httpd" "FH1201" "v1"

# # NETGEAR latest version
# analyze_binary "R6300v2-V1.0.4.36/httpd" "R6300v2" "V1.0.4.36"
# analyze_binary "R6400v2-v1.0.4.84/httpd" "R6400" "v1_0_4_84"
# analyze_binary "R6700-v1.0.2.8/httpd" "R6700" "v1_0_2_8"
# analyze_binary "R7000P-V1.3.1.64/httpd" "R7000P" "V1.3.1.64"
# analyze_binary "R7300-V1.0.0.74/httpd" "R7300" "V1.0.0.74"
# analyze_binary "R7500v2-V1.0.3.46/net-cgi" "R7500v2" "V1.0.3.46"
# analyze_binary "R7900-V1.0.4.22/httpd" "R7900" "V1.0.4.22"
# analyze_binary "R8000-V1.0.4.52/httpd" "R8000" "V1.0.4.52"
# analyze_binary "R8300-V1.0.2.130/httpd" "R8300" "V1.0.2.130"
# analyze_binary "R8900-V1.0.5.14/net-cgi" "R8900" "V1.0.5.14"
# # analyze_binary "XR500-V2.3.2.56/net-cgi" "XR500" "V2.3.2.56"
# analyze_binary "DGN1000-v1.1.00.56/setup.cgi" "DGN1000" "v1_1_00_56"
# analyze_binary "DGN2200-V1.0.0.58/httpd" "DGN2200" "V1.0.0.58"
# analyze_binary "WNR3500Lv2-V1.2.0.56/httpd" "WNR3500Lv2" "V1.2.0.56"
 
# # TP-Link latest version
# analyze_binary "TL-WR940N_US_V5_200316/httpd" "TL-WR940N_US" "V5_200316"

# # D-Link latest version
# analyze_binary "DIR645A1_FW105B01/cgibin" "DIR645A1" "FW105B01"
# analyze_binary "DIR890LA1_FW111b04/cgibin" "DIR890LA1" "FW111b04"

# analyze_binary "US_WH450AV1.0BR_V2.0.0.1/httpd" "US_WH450A" "V1.0BR_V2.0.0.1"

# analyze_binary "R6400-V1.0.1.46/httpd" "R6400" "V1.0.1.46"
