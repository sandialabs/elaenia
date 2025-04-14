import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

import math


# eps
def eps(e): 
    return pow(2, e-(53 - 1)) / 2

# get the ulp of a binade
def ulp_bin(e):
    return math.ulp(pow(2,e) + ((pow(2,e+1) - pow(2,e)) / 2))

err_csv = pd.read_csv("data/sin/sin-data.csv")
analysis = pd.read_csv("data/sin/sin-mine2.csv")

# Plotting
# -----------------------


fig = plt.figure(facecolor="w", figsize=(8,4))
ax = fig.add_subplot()
err_csv.plot.scatter(x="mpfr_out", y="err", secondary_y=["mpfr_out", "dbl_out"], ax=ax)
fig.suptitle('Fluctuat vs Step Functions for $\mathit{sin}(x)$')
ax.set_xlabel('$\mathit{sin}(x)$')
ax.set_ylabel('error')
ax.set_ylim([0,10.142295543382296635861554772191e-16])
ax.set_xlim([0,1])

plt.hlines(y=5.181361907848536e-16, xmin=0, xmax=1, color='r', label='fluctuat')
#plt.hlines(y=8.0e-16, xmin=0,xmax=1,color='r')

# Step function
print('sorting...')
analysis.sort_values(by = 'low', ascending=False, inplace=True)
analysis.reset_index(inplace=True, drop=True)
print('drawing step functions...')
for i, row in analysis[analysis['var'] == 'y'].iterrows():
    if math.isnan(float(row['low'])):
        continue
    plt.hlines(y=float(row['err']), xmin=float(row['low']), xmax=float(row['high']), color='g', label='step')
    if i < analysis.shape[0] - 1:
        n = analysis.iloc[i + 1]
        ymin, ymax = (row['err'], n['err']) if float(row['err']) < float(n['err']) else (n['err'], row['err'])
        plt.vlines(x=float(row['low']), ymin=float(ymin), ymax=float(ymax), color='g')
        '''
        if abs(float(ymax) - float(ymin)) > float('.2e-15'):
            print(row)
            print(n)
            print(ymin)
            print(ymax)
            print(float(ymax) - float(ymin))
            input()
        '''
handles, _ = ax.get_legend_handles_labels()
plt.legend(handles = handles[0:2], labels = ['Fluctuat', 'Step Functions'], loc='upper left')
#plt.legend([], ['Fluctuat', 'Step Functions']loc='upper left')

# Ulp and machine eps
# -----------------------
#plt.axhspan(ymin=eps, ymax=eps, xmin=0, xmax=1, color='r', linestyle = '-')
#for e in range(-4, 0):
#    plt.hlines(y=eps(e), xmin=pow(2,e), xmax=pow(2,e+1), color='r', linestyle='-')
#    plt.hlines(y=ulp_bin(e), xmin=pow(2,e), xmax=pow(2,e+1), color='b', linestyle='-')

# binades
# -----------------------
#plt.axvline(x=pow(2, -1), color='r', linestyle = 'dashed')
#plt.axvline(x=pow(2, -2), color='r', linestyle = 'dashed')
#plt.axvline(x=pow(2, -3), color='r', linestyle = 'dashed')
##plt.axvline(x=pow(2, -4), color='r', linestyle = '-')
#plt.text(pow(2, -1) - 0.05, y=0.95e-15, s='$2^{-1}$')
#plt.text(pow(2, -2) - 0.05, y=0.95e-15, s='$2^{-2}$')
#plt.text(pow(2, -3) - 0.05, y=0.95e-15, s='$2^{-3}$')
##plt.text(pow(2, -4), y=2.5*pow(10,-16), s='2^-4')

plt.savefig('sin-error.png', dpi=600)
plt.show()

plt.close("all")
