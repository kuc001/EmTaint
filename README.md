# EmTaint

`EmTaint`, a novel static analysis tool for accurate and fast detection of taint-style vulnerabilities in embedded firmware. 
In EmTaint, we design a structured symbolic expression-based (SSE-based) on-demand alias analysis technique, which serves as a basis for resolving both implicit data flow and control flow on potential vulnerable paths. Based on it, we come up with indirect call resolution and accurate taint analysis scheme. Combined with sanitization rule checking, EmTaint can eventually discovers a large number of taint-style vulnerabilities accurately within a limited time.


## Getting Started

### Requirements

`EmTaint`'s execution environment depends on Angr, which we packaged as an docker image and published to the hub (NOTE: thare are some issues in uploading the large docker image file to zenodo, so we upload it to docker hub instead.). The source code for `EmTaint` is **EmTaint.tar.gz**.
We can execute following commands to start the experiment verification.
We suggest users to use Linux system as the host machine.

```
docker pull doneme123/emtaint:v1.1
tar -zxvf EmTaint.tar.gz
cd EmTaint
docker run -ti --rm -v `pwd`:/work doneme123/emtaint:v1.1
cd /work
workon EmTaint
```


### Basic functionality
We run the following command to test indirect-call resolution and vulnerability detection for binary `httpd` in firmware `R8000_v1.0.4.4`.

```
bash run.sh main.py ./firmware-binaries/
```

Estimated Time < 15min

Expected Output: The result will be saved in file **R8000_v1_0_4_4.json** in directory **./data/result_data/**.

The basic functionality of `EmTaint` is evaluated from three aspects: vulnerability discovery, effectiveness and efficiency of indirect call resolution,
and effectiveness in finding vulnerability with or without indirect call resolution.


#### Evaluation for vulnerability discovery

```
python collect_result.py ./data/result_data/R8000_v1_0_4_4.json alert
```

Expected Output: the result show the alerts produced by `EmTaint` for binary `httpd` in firmware `R8000_v1.0.4.4`.


#### Evaluation for Effectiveness and Efficiency of indirect call resolution

```
python collect_result.py ./data/result_data/R8000_v1_0_4_4.json icall
```

Expected Output: the result show the effectiveness and efficiency of indirect call resolution for binary `httpd` in firmware `R8000_v1.0.4.4`.


#### Evaluation for Effectiveness in finding vulnerability with or without indirect call resolution

```
python collect_result.py ./data/result_data/R8000_v1_0_4_4.json compare
```

Expected Output: the result show the effectiveness and necessity of indirect call resolution for finding vulnerabilities in embedded firmware.


## Detailed Description
In Getting Started section, we only evaluate the `EmTaint` on one binary in a firmware image.
In Detailed Description, we describe the evaluation of all claims as follows.
For vulnerability discovery and indirect call resolution evaluation,
we can evaluate it on all 35 firmware images by modifying shell script `run.sh`, where `run.sh` includes commands to evaluate 35 fimware images.
We put 32 firmware-related binaries in directory `firmware-binaries/`.
For example, the code in `run.sh` below will evaluate firmware `RV130_v.1.0.3.44` for vulnerability discovery and indirect call resolution.

```
analyze_binary "rv130_v44/httpd" "rv130" "1_0_3_44"
```
Expected Output: The result will be saved in file **rv130_1_0_3_44.json** in directory **./data/result_data/**.

In addition to the above methods, we can also run the following command to evaluate the functionality of `EmTaint` respectively.

```bash
# Indirect call resolution
python main.py -f ./firmware-binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 -i

# vulnerability discovery with indirect call resolution
python main.py -f ./firmware-binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 -t

# vulnerability discovery without indirect call resolution
python main.py -f ./firmware-binaries/rv130_v44/httpd -n rv130 -v 1_0_3_44 -t --resolve_icall 0
```


## Extension
If the user obtain another firmware, which is not involved in our dataset, you can follow the instructions to attemp to run it in `EmTaint`.

1) Use tool `binwalk` (https://github.com/ReFirmLabs/binwalk) to extract the binaries associated with handling network requests in the firmware.
2) Extract the binary information by running script `./dataflow/ida_plugin/parse_arm_binary.py` in the IDA Pro, which generates two files, `{binary-name}_cfg.json` and `{binary-name}_block_info.json`.
3) Create directory `./data/ida_data/{name}_{version}` and copy the above two files to it.
4) Finally, run command `python main.py -f {binary} -n {name} -v {version} -t` to perform vulnerability discovery.







