import subprocess
from subprocess import check_output

trials = range(25, 800, 25)

output_strs = []

for trial_num in trials:
    output = check_output(["time", "racket", "binomial_perf_2.rkt", str(trial_num)], stderr=subprocess.STDOUT)
    print(f"Finished trial {trial_num}")
    output_strs.append(output.decode("utf-8"))

raw_results = zip(trials, output_strs)

def to_sec(time):
    if ":" in time:
        split_time = time.strip().split(":")
        return float(split_time[1]) + (60.0 * split_time[0])
    else:
        return float(time)


results = []
for trial, s in raw_results:
    ret, times = s.strip().split("\n")
    split_times_strs = times.strip().split()
    result = {
        "trial": trial,
        "value": ret,
        "real_time": to_sec(split_times_strs[0]),
        "user_time": to_sec(split_times_strs[2]),
        "sys_time": to_sec(split_times_strs[4]),
    }
    results.append(result)

#print(results)

# want a csv with: trial_num, output, time_real, time_user, time_sys

with open("25_800_25_binomial_perf_2.csv", "w") as file:
    for result in results:
        file.write(f'{result["trial"]},"{result["value"]}",{result["real_time"]},{result["user_time"]},{result["sys_time"]}\n')
    file.close()
