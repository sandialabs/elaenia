set.seed(42)
n <- 10000

# e.g.,
# 20.0	0.5	5e-5	5e-7	5e-10	5e-13	5e-14	1.05	5e-5	5e-7	5e-10	128.0;
# Should probably use latin hypercube sampling, but oh well
t   <- runif(n, min = -35.  ,  max =  80.)
b0  <- runif(n, min = -1.   ,  max =  1.)
b1  <- runif(n, min = -1e-4 ,  max =  1.e-4)
b2  <- runif(n, min = -1e-6 ,  max =  1.e-6)
b3  <- runif(n, min = -1e-9 ,  max =  1.e-9)
b4  <- runif(n, min = -1e-12,  max =  1.e-12)
b5  <- runif(n, min = -1e-13,  max =  1.e-13)
s0  <- runif(n, min = -0.9  ,  max =  1.1)
s1  <- runif(n, min = -1e-4 ,  max =  1.e-4)
s2  <- runif(n, min = -1e-6 ,  max =  1.e-6)
s3  <- runif(n, min = -1e-9 ,  max =  1.e-9)
ain <- runif(n, min = -256. ,  max =  256.)

df  <- cbind(t,b0,b1,b2,b3,b4,b5,s0,s1,s2,s3,ain)

write.table(df,'temp-herbie.csv',
	quote=FALSE, row.names=FALSE, col.names=FALSE, sep='\t')

