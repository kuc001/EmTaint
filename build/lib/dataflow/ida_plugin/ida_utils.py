#!/usr/bin/env python3

import os
import configparser

# IDA_PATH_32 = '/home/kai/idapro/idat'
# IDA_PATH_64 = '/home/kai/idapro/idat64'
# IDB_STORE_PATH = '/tmp/'


def parse_cfg_info(binary_path, ida_data_path, config_file):
    """
    Use IDA Pro to parse binary and get cfg and data ref info.
    """
    config = configparser.ConfigParser()
    config.read(config_file)
    ida_engine_path = config.get('ida_config', 'IDA_ENGINE_PATH')
    idb_save_path = config.get('ida_config', 'IDB_SAVE_PATH')
    # ida_data_path = os.path.join(current_path, config.get('result_config', 'IDA_DATA_PATH'))

    ida_start = config.get('scripts_config', 'IDA_START')
    ida_get_cfg = config.get('scripts_config', 'IDA_GET_CFG')
    print("start analyze binary using ida...")

    if os.path.exists(ida_engine_path):
        os.system('%s %s %s %s' % (ida_start, ida_engine_path, binary_path, idb_save_path))
        os.system("TVHEADLESS=1 %s -A -S'%s %s ' %s > /dev/null" % (ida_engine_path, ida_get_cfg, ida_data_path, idb_save_path))
        # print("idb-path: %s" % (idb_save_path))
        # os.system("%s -S'%s %s ' %s" % (ida_engine_path, ida_get_cfg, ida_data_path, idb_save_path))
