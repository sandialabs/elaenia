import pandas as pd
import matplotlib
import matplotlib.pyplot as plt
import numpy as np

import math
import sys
# 1st argument is exact data
# 2nd argument is my data
# 3rd argument is the function being compared run
# 4th argument is if we should show binades
# 5th argument is the variable to check
# 6th argument is whether to compare with fluctuat
# 7th argument is how to scale y-axis (default: linear)
# 8th argument is where to put legend
# 9th argument whether to have density colorbar
exact_csv = sys.argv[1]
my_csv = sys.argv[2]
fun = sys.argv[3]
show_binades = sys.argv[4].lower() == 'true'
var = sys.argv[5]

if len(sys.argv) > 6:
    compare = sys.argv[6].lower() == 'true'
else:
    compare = False

if len(sys.argv) > 7:
    logscale = sys.argv[7].lower() == 'log'
    if logscale:
        print("Log scale y-axis")
else:
    logscale = False

if len(sys.argv) > 8:
    legend_loc = sys.argv[8].lower()
else:
    legend_loc = 'best'

if len(sys.argv) > 9:
    use_colorbar = sys.argv[9].lower() == 'colorbar'

if len(sys.argv) > 10:
    branch_instability = sys.argv[10].lower() == 'bi'
else:
    branch_instability = False

print('reading CSVs...')
err_csv = pd.read_csv(exact_csv,dtype="float64")
analy = pd.read_csv(my_csv)
analysis = analy.copy()

# Set some colors and plot settings
col_comp = '#d95f02'
col_step = '#1b9e77'
col_bin  = '#acacac'
col_bi   = '#e7298a'

# Crunch the numbers
# -----------------------
range_lo, range_hi = min(err_csv.dbl_out), max(err_csv.dbl_out)
print('sorting...')
#analysis= analysis.filter(items=['z'], axis=0)

# We treat sin special :)
if my_csv == 'data/sin/sin-mine-good.csv': # Old analysis used var y
    var = 'y'
    xlab_var = 'x'
    analysis = analysis[analysis['var'] == var]
    cmap = 'Blues'
    if exact_csv == 'data/sin-exp.csv':
        figsize = (5,2.5)
    else:
        figsize = (8,4)
else:
    xlab_var = var
    analysis = analysis[analysis['var'] == var]
    cmap = matplotlib.cm.Blues(np.linspace(0,1,30))
    # 0: --> start at 0%, 15: --> Start at 50%
    cmap = matplotlib.colors.ListedColormap(cmap[6:,:-1])
    figsize = (5,2.5)

analysis["low"] = analysis["low"].astype(float)
analysis["high"] = analysis["high"].astype(float)

analysis['low'] = analysis["low"].clip(lower=range_lo, upper=range_hi)
analysis['high'] = analysis["high"].clip(lower= range_lo, upper=range_hi)

analysis.sort_values(by='err', ascending=False, inplace=True)
analysis.drop_duplicates(subset=['low', 'high'], inplace=True)
# analysis = analysis[(range_lo <= analysis["low"]) & (analysis["low"] <= range_hi)]
# analysis = analysis[(range_lo <= analysis["high"]) & (analysis["high"] <= range_hi)]

analysis.sort_values(by='low', ascending=False, inplace=True)
analysis.reset_index(inplace=True, drop=True)

# Other tools
# -----------------------
print("Adding other tool's values...")
fluctuat_values = {
    'sin':          5.181361907848536e-16, 
    'simple-sub':   1.859623566247137e-15, 
    'branch':       7.652212197228893e-15,
    'determinant':  1.904254531837068e-12,
    'doppler1':     3.451998544471651e-13,
    'rigidBody1':   2.131628207280301e-13,
    'rigidBody2':   2.27160512622504e-11,
    'jetEngine':    1.938270347097141e-08,
    'turbine1':     4.921500999446206e-14,
    'turbine2':     6.448041039386743e-14,
    'turbine3':     3.701711270192855e-14,
    'verhulst':     1.978064344264455e-16,
    'predatorPrey': 1.051344891698721e-16,
    'carbonGas':    1.575554835234155e-08,
    'sqroot':       5.620504062164855e-16,
    'sineOrder3':   5.986570354693264e-16,
    'cav10':        1.4210854715202e-14,    # This is ignoring the branch instability
    'cav10-bi':     101,                    # With branch instability
    'bspline3':     5.088522196198635e-17
}
fptaylor_values = {'simple-sub': 2.735590e-15}
precisa_values = {'simple-branch': 7.638334409421077e-15}

if compare:
    compared_tool = fluctuat_values[fun]
else:
    compared_tool = min(analysis.err)

# Minimum and Maximum predicted errors
max_err = max(max(analysis.err), compared_tool)
min_err = min(min(analysis.err), compared_tool)

# Plotting
# -----------------------
# Have to do all this nonsense because Matplotlib is stupid (and non ggplot).
# Messing with global variables, what is this, 1985?

# y-axis log is not supported, you have to do it manually
if logscale:
    # np.logspace takes in the exponent of the min and the exponent of the max
    bins = (np.linspace(range_lo,range_hi,160), np.logspace(math.log(min_err / (1e13),10),math.log(max_err,10),80,base=10))
else:
    bins = [160,80]

# Basic setup
plt.figure(facecolor="w", figsize=figsize)
    
#err_csv.plot.scatter(x="C[0]_mpfr", y="C[0]_err", secondary_y=["mpfr_out", "dbl_out"], ax=ax)
# err_csv.plot.scatter(x="mpfr_out", y="err", secondary_y=["mpfr_out", "dbl_out"], ax=ax)

if logscale:
    # matplotlib.colorbar(ax.pcolormesh(bins[0], bins[1], counts.T))
    # ax.set_ylim(ymin=bins[1][0], ymax=bins[1][-1])
    counts, _, _ = np.histogram2d(
        x=err_csv["mpfr_out"], y=err_csv["err"], 
        bins=bins)
    ax = plt.gca()
    ax.pcolormesh(bins[0], bins[1], counts.T, cmap=cmap,
                  norm=matplotlib.colors.LogNorm())
    ax.set_yscale('log')
    ax.set_ylim(top=400)
else:
    counts, xedges, yedges, img = plt.hist2d(
        x=err_csv["mpfr_out"], y=err_csv["err"],
        range=np.array([(range_lo, 1.00*range_hi), (0, 1.05*max_err)]),
        bins=bins, cmin=1, norm=matplotlib.colors.LogNorm(), cmap=cmap)

if fun == 'doppler1' or fun == 'rigidBody1':
    plt.suptitle('Step Functions for {}$(\\mathit{{x_1,x_2,x_3}})$'.format(fun), x = 0.90, ha='right')
else:
    plt.suptitle('Step Functions for {}$(\\mathit{{x}})$'.format(fun), x = 0.90, ha='right')
ax = plt.gca()

ax.set_xlabel('{}'.format(fun))
ax.set_ylabel('Absolute Error')

# To handle the monstrosity that is cav10
if fun == 'cav10':
    ax.set_ylim(top=800)
    if branch_instability:
        branch_unstable = fluctuat_values[f"{fun}-bi"]
        print("Branch instability result: {}".format(branch_unstable))
        ax.hlines(y=branch_unstable, color=col_comp, label='fluctuat-branch-unstable', xmin=range_lo, xmax=range_hi)
        plt.figtext(0.05,-0.03, "branch instability: on")
    else:
        plt.figtext(0.05,-0.03, "branch instability: off")


# Step function drawing
# -----------------------
steps = analysis.shape[0]
print('drawing step functions...')
for i, row in analysis[analysis['var'] == var].iterrows():
    if math.isnan(float(row['low'])): continue

    # Infinity?
    err = ax.get_ylim()[1] if float(row['err']) == float("inf") else float(row['err'])

    # Horizontal line for the segment
    ax.hlines(y=err,
               xmin=float(row['low']), xmax=float(row['high']), 
               color=col_step, label='step')

    # Vertical lines
    # if i < steps - 1:
    #     n = analysis.iloc[i + 1]
    #     ymin, ymax = (err, n['err']) if err < float(n['err']) else (n['err'], err)
    #     plt.vlines(x=float(row['low']), ymin=float(ymin), ymax=float(ymax), color='r')

# Plot infinite values

# binades
# -----------------------
note_y = max_err * 0.95
if show_binades:
    print("displaying binades")
    ax.axvline(x=pow(2, -1), color=col_bin, linestyle = 'dashed', lw=1)
    ax.axvline(x=pow(2, -2), color=col_bin, linestyle = 'dashed', lw=1)
    ax.axvline(x=pow(2, -3), color=col_bin, linestyle = 'dashed', lw=1)
    ax.axvline(x=pow(2, -4), color=col_bin, linestyle = 'dashed', lw=1)
    ax.text(pow(2, -1) - 0.05, y=note_y, s='$2^{-1}$')
    ax.text(pow(2, -2) - 0.05, y=note_y, s='$2^{-2}$')
    ax.text(pow(2, -3) - 0.05, y=note_y, s='$2^{-3}$')
    ax.text(pow(2, -4) - 0.05, y=note_y, s='$2^{-4}$')

# Legend
# -----------------------
print("Creating legend...")
handles, _ = ax.get_legend_handles_labels()
#plt.axhline(y=fptaylor_values['simple-sub'], color=col_comp, label='fptaylor', linestyle='dashed')
#plt.axhline(y=precisa_values['simple-branch'], color=col_comp, label='precisa', linestyle='dashed')
#plt.axhline(y=fluctuat_values['determinant'], color=col_comp, label='fluctuat', linestyle='dashed')
#plt.legend(handles = handles[0:3], labels = ['Fluctuat', 'FPTaylor', 'Step Functions'], loc='upper left')
#plt.legend(handles = handles[0:2], labels = ['Fluctuat', 'Step Functions'], loc='upper left')
#plt.legend(handles = handles[0:1], labels = ['Step Functions'], loc='upper right')

if compare and not branch_instability:
    handles = handles[0:2]
    labels = ['Step Functions', 'Fluctuat']
    ax.hlines(y=compared_tool, color=col_comp, label='fluctuat', xmin=range_lo, xmax=range_hi)
else:
    handles = handles[0:1]
    if fun == 'sin':
        labels = ['Error Bound']
    else:
        labels = ['Step Functions']

if legend_loc == 'outside':
    legend_loc = 'center left'
    bbox = (1.0,0.5)
elif legend_loc != 'nolegend':
    bbox = None
    ax.legend(handles = handles[0:1], labels = ['Error Bound'], loc=legend_loc)

if legend_loc != 'nolegend':
    # Adding default bbox_to_anchor seems to mess things up
    ax.legend(handles=handles, labels=labels, loc=legend_loc)
    leg = ax.get_legend()
    if compare:
        leg.legend_handles[1].set_color(col_comp)

if legend_loc == 'outside':
    ax.legend(handles=handles, labels=labels, loc=legend_loc, bbox_to_anchor=bbox)

if use_colorbar:
    plt.gcf().colorbar(img, label = "sample density", pad = 0.02, ax=ax)

# Annotations
if fun == 'sin' and exact_csv == 'data/sin/sin-data.csv': # Horrible hack
    plt.figtext(0.66,-0.03, "# samples = {:,}\n# segments = {:,}".format(len(err_csv), steps))
else:
    plt.figtext(0.66,-0.03, "# segments = {:,}".format(steps))

# Print useful info
print("# samples = {:,}\n# segments = {:,}\n".format(
    len(err_csv), steps))
print("domain in [{},{}]\nerror in [{},{}]".format(
    range_lo, range_hi, min(min(analysis.err), compared_tool), max_err))
if compare and len(err_csv[err_csv.err > compared_tool]) > 0:
    print("This should never happen. Worst-case error > fluctuat's bound of {:.15e}, {} times".format(
        compared_tool, len(err_csv[err_csv.err > compared_tool])))
    pd.set_option('display.float_format', lambda x: '%.15e' % x)
    print(err_csv[err_csv.err > compared_tool].head().to_string())
# TODO: Check for our tool, which is more complex since it's per-segment


#plt.show()

if logscale:
    out_file = 'results/{}-error{}.pdf'.format(fun,("-cmp" if compare else ""))
else:
    out_file = 'results/{}-error{}.pdf'.format(fun,("-cmp" if compare else ""))
print(f"saving figure to {out_file} ...")

if logscale:
    plt.savefig(out_file, dpi=600, bbox_inches = "tight")
else:
    plt.savefig(out_file, dpi=600, bbox_inches = "tight")

# plt.close("all")
