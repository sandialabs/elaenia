# Source: https://statisticsbyjim.com/basics/bimodal-distribution/
# Weber, NA (1946). “Dimorphism in the African Oecophylla worker and an anomaly (Hym.: Formicidae),” Annals of the Entomological Society of America. 39: 7–10.
df <- read.table('bimodal.csv', header=TRUE, sep=',')
h <- hist(df$Bimodal, probability = TRUE, n = 15)
paste0(h$mids, collapse = ", ")
paste0(h$density, collapse = ", ")

