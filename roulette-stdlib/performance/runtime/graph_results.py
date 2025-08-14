import math
import matplotlib.pyplot as plt

trials = []
times = []

with open("25_800_25_binomial_perf_2.csv", "r") as file:
    for line in file:
        row = line.strip().split(",")
        trials.append(int(row[0]))
        times.append(float(row[2]))


y_axis_max = math.ceil(max(times))
spacing = math.ceil(y_axis_max / len(times))
y_axis = range(0, y_axis_max + spacing, spacing)

plt.plot(trials, times, marker="o")
plt.yticks(y_axis)
plt.xlabel("Trials")
plt.ylabel("Time (seconds)")
plt.title("Roulette Binomial Implementation Performance")
plt.show()
