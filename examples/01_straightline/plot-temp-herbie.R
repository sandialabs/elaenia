library(ggplot2)
library(reshape2)

df <- read.table('temp-herbie-out.csv', header=TRUE, sep='\t')
n <- nrow(df)

df$dp_orig <- abs((df$mpfr - df$orig)/df$mpfr)
df$herbie_alt2 <- abs((df$mpfr - df$alt2)/df$mpfr)
df$herbie_ite  <- abs((df$mpfr - df$ite)/df$mpfr)
df$herbie_alt7 <- abs((df$mpfr - df$alt7)/df$mpfr)
# MPFR, orig, alt2, ite, alt7
speedup <- c(1.0, 2.6, 5.5, 9.6)


dfm <- melt(df, id.vars=c('mpfr','orig','alt2','ite','alt7'),
	variable.name="Program", value.name="rel_err")

p <- ggplot(dfm, aes(x=Program, y=rel_err)) +
	geom_point(size=1, position=position_jitter(w=0.2, h=0)) +
	scale_y_log10(limits = c(1e-16,1),
                      breaks = c(1e-16,1e-13,1e-10,1e-7,1e-4,1e-1,1)) +
	annotate("text", x=c(1, 2, 3, 4), y=1e-11,
	         label = paste0("speedup ", speedup, "x")) +
	labs(title = 'Relative error of Herbie rewrites',
	     y = 'Relative Error',
	     caption = paste0("n = ", prettyNum(n, big.mark=",")))


ggsave('rel_err.pdf')
