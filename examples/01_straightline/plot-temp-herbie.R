library(ggplot2)
library(reshape2)

df <- read.table('temp-herbie-out.csv', header=TRUE, sep='\t')
n <- nrow(df)

df$dp_orig <- abs((df$mpfr - df$orig)/df$mpfr)
df$herbie_alt2 <- abs((df$mpfr - df$alt2)/df$mpfr)
df$herbie_ite  <- abs((df$mpfr - df$ite)/df$mpfr)
df$herbie_alt7 <- abs((df$mpfr - df$alt7)/df$mpfr)


dfm <- melt(df, id.vars=c('mpfr','orig','alt2','ite','alt7'),
	variable.name="program", value.name="rel_err")

p <- ggplot(dfm, aes(x=program, y=rel_err)) +
	geom_point(size=1, position=position_jitter(w=0.2, h=0)) +
	scale_y_log10(limits = c(1e-16,NA),
                      breaks = c(1e-16,1e-13,1e-10,1e-7,1e-4,1e-1,1e2)) +
	labs(title = 'Relative error of Herbie rewrites',
	     caption = paste0("n = ", prettyNum(n, big.mark=",")))


ggsave('rel_err.pdf')
