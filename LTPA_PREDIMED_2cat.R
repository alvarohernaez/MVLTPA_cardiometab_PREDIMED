rm(list=ls())

# EXECUTE ALL - OPEN INSTALLED PACKAGES

library(acepack)
library(arm)
library(backports)
library(base64enc)
library(bitops)
library(boot)
library(car)
library(caTools)
library(checkmate)
library(chron)
library(cobalt)
library(colorspace)
library(compareGroups)
library(data.table)
library(DescTools)
library(dichromat)
library(digest)
library(dplyr)
library(evaluate)
library(foreign)
library(Formula)
library(gam)
library(ggplot2)
library(ggpubr)
library(gplots)
library(gratia)
library(gridExtra)
library(gtable)
library(haven)
library(highr)
library(Hmisc)
library(htmlTable)
library(htmltools)
library(htmlwidgets)
library(icenReg)
library(irr)
library(jsonlite)
library(keras)
library(knitr)
library(labeling)
library(latticeExtra)
library(lazyeval)
library(lme4)
library(lmerTest)
library(lmtest)
library(MASS)
library(magrittr)
library(markdown)
library(MatrixModels)
library(meta)
library(metafor)
library(mgcv)
library(missRanger)
library(mime)
library(minqa)
library(MuMIn)
library(munsell)
library(nephro)
library(nlme)
library(pbkrtest)
library(plotrix)
library(plyr)
library(psy)
library(purrr)
library(quantreg)
library(RColorBrewer)
library(Rcpp)
library(RcppEigen)
library(rlang)
library(ROCR)
library(RODBC)
library(reshape2)
library(sandwich)
library(scales)
library(smoothHR)
library(SparseM)
library(standardize)
library(stringi)
library(stringr)
library(survival)
library(survminer)
library(tibble)
library(tidyr)
library(vcd)
library(viridis)
library(viridisLite)
library(WeightIt)
library(yaml)

# OPEN PRE-GENERATED FUNCTIONS

RutinesLocals<- "D:/R/Rutinas"
source(file.path(RutinesLocals,"carrega.llibreria.r"))
source(file.path(RutinesLocals,"merge2.r"))
source(file.path(RutinesLocals,"fix2.r"))
source(file.path(RutinesLocals,"table2.r"))
source(file.path(RutinesLocals,"subset2.r"))
source(file.path(RutinesLocals,"format2.r"))
source(file.path(RutinesLocals,"order2.r"))
source(file.path(RutinesLocals,"intervals.r"))

# OPEN MY OWN FUNCTIONS TO PUT RESULTS IN NICE FORMAT ("guapa")

guapa<-function(x)
{
  redondeo<-ifelse(abs(x)<0.00001,signif(x,1),
                   ifelse(abs(x)<0.0001,signif(x,1),
                          ifelse(abs(x)<0.001,signif(x,1),
                                 ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                        ifelse(abs(x)<1,sprintf("%.2f",round(x,2)),
                                               ifelse(abs(x)<10,sprintf("%.2f",round(x,2)),
                                                      ifelse(abs(x)<100,sprintf("%.1f",round(x,1)),
                                                             ifelse(abs(x)>=100,round(x,0),round(x,0)))))))))
  return(redondeo)
}

ic_guapa<-function(x,y,z)
{
  ic<-paste(x," [",y,"; ",z,"]",sep="")
  return(ic)
}

ic_guapa2<-function(x,y,z)
{
  ic<-paste(x," (",y," to ",z,")",sep="")
  return(ic)
}

pval_guapa<-function(x)
{
  pval<-ifelse(x<0.00001,"<0.00001",
               ifelse(x<0.001,"<0.001",
                      ifelse(abs(x)<0.01,sprintf("%.3f",round(x,3)),
                             ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                    ifelse(abs(x)<1,sprintf("%.3f",round(x,3)),guapa(x))))))
  return(pval)
}

pval_guapa2<-function(x)
{
  pval<-ifelse(x<0.00001," < 0.00001",
               ifelse(x<0.001," < 0.001",
                      ifelse(abs(x)<0.01,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                             ifelse(abs(x)<0.1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),
                                    ifelse(abs(x)<1,paste(" = ",sprintf("%.3f",round(x,3)),sep=""),guapa(x))))))
  return(pval)
}

mean_ic_guapa <- function(x, na.rm=FALSE) 
{
  if (na.rm) x <- na.omit(x)
  se<-sqrt(var(x)/length(x))
  z<-qnorm(1-0.05/2)
  media<-mean(x)
  ic95a<-guapa(media-(z*se))
  ic95b<-guapa(media+(z*se))
  media<-guapa(media)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

mean_sd_guapa <- function(x) 
{
  media<-guapa(mean(x, na.rm=TRUE))
  sd<-guapa(sd(x, na.rm=TRUE))
  end<-paste(media," (",sd,")",sep="")
  return(end)
}

beta_se_ic_guapa <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

beta_se_ic_guapa2 <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa2(media,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa2 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa3 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-round(exp(x),3)
  ic95a<-round(exp(x-(z*y)),3)
  ic95b<-round(exp(x+(z*y)),3)
  ic_ok<-ic_guapa2(hr,ic95a,ic95b)
  return(ic_ok)
}

header.true <- function(df)
{
  names(df) <- as.character(unlist(df[1,]))
  df[-1,]
}

z<-qnorm(1-0.05/2)
se <- function(x) sqrt(var(x) / length(x))

closest<-function(xv,sv){
  xv[which(abs(xv-sv)==min(abs(xv-sv)))] }

options(scipen=999)

setwd("D:/Artículos/Eleonora - LTPA PREDIMED")


# CREATE WORKING DIRECTORY AND OPEN IT

dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Data")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/bmi")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/bmi/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/bmi/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/bmi/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/wc")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/wc/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/wc/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/wc/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/whtr")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/whtr/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/whtr/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/whtr/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/sbp")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/sbp/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/sbp/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/sbp/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/dbp")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/dbp/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/dbp/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/tc")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/tc/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/tc/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/ldlc")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/ldlc/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/ldlc/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/ldlc/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/ldlc_hdlc")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/ldlc_hdlc/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/ldlc_hdlc/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hdlc")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hdlc/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hdlc/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hdlc/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/tg")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/tg/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/tg/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/tg/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/gluco")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/gluco/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/gluco/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/gluco/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hb1ac")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hb1ac/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hb1ac/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/hb1ac/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/egfr")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/egfr/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/egfr/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/egfr/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/nlr")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/nlr/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/nlr/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/nlr/Survival")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/plat")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/plat/Descriptive")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/plat/Repeated")
dir.create("D:/Artículos/Eleonora - LTPA PREDIMED/Outputs2/plat/Survival")


################
### ANALYSES ###
################

rm(list = ls(envir=.GlobalEnv)[sapply(ls(envir=.GlobalEnv),
                                      function(x) inherits(get(x, envir = .GlobalEnv), c("data.frame", "tbl_df")))], envir = .GlobalEnv)
setwd("D:/Artículos/Eleonora - LTPA PREDIMED")

# DESCRIPTIVE TABLES, we use the "wide" datasets + NAs #

# Checking normal distribution in continuous variables
#plot(compareGroups(~mvltpalong,data=dat))

# BMI

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$bmi_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/bmi/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$bmi_ok==1,]

vars01<-c("bmi00","bmi01","bmi02","bmi03","bmi04","bmi05","bmi06","bmi07","bmi08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("bmi")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/bmi/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$bmi_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(bmi), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/bmi/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# wc

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$wc_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/wc/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$wc_ok==1,]

vars01<-c("wc00","wc01","wc02","wc03","wc04","wc05","wc06","wc07","wc08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("wc")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/wc/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$wc_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(wc), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/wc/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# whtr

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$wc_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/whtr/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$wc_ok==1,]

vars01<-c("whtr00","whtr01","whtr02","whtr03","whtr04","whtr05","whtr06","whtr07","whtr08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("whtr")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/whtr/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$wc_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(whtr), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/whtr/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# sbp

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$sbp_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/sbp/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$sbp_ok==1,]

vars01<-c("sbp00","sbp01","sbp02","sbp03","sbp04","sbp05","sbp06","sbp07","sbp08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("sbp")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/sbp/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$sbp_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(sbp), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/sbp/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# dbp

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$dbp_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/dbp/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$dbp_ok==1,]

vars01<-c("dbp00","dbp01","dbp02","dbp03","dbp04","dbp05","dbp06","dbp07","dbp08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("dbp")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/dbp/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$dbp_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(dbp), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/dbp/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# tc

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$lipids_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/tc/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$lipids_ok==1,]

vars01<-c("tc00","tc01","tc02","tc03","tc04","tc05","tc06","tc07","tc08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("tc")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/tc/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$lipids_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(tc), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/tc/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# hdlc

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$lipids_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/hdlc/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$lipids_ok==1,]

vars01<-c("hdlc00","hdlc01","hdlc02","hdlc03","hdlc04","hdlc05","hdlc06","hdlc07","hdlc08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("hdlc")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/hdlc/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$lipids_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(hdlc), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/hdlc/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# ldlc

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$lipids_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/ldlc/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$lipids_ok==1,]

vars01<-c("ldlc00","ldlc01","ldlc02","ldlc03","ldlc04","ldlc05","ldlc06","ldlc07","ldlc08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("ldlc")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/ldlc/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$lipids_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(ldlc), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/ldlc/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# ldlc_hdlc

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$lipids_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/ldlc_hdlc/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$lipids_ok==1,]

vars01<-c("ldlc_hdlc00","ldlc_hdlc01","ldlc_hdlc02","ldlc_hdlc03","ldlc_hdlc04","ldlc_hdlc05","ldlc_hdlc06","ldlc_hdlc07","ldlc_hdlc08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("ldlc_hdlc")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/ldlc_hdlc/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$lipids_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(ldlc_hdlc), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/ldlc_hdlc/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# tg

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$lipids_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/tg/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$lipids_ok==1,]

vars01<-c("tg00","tg01","tg02","tg03","tg04","tg05","tg06","tg07","tg08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("tg")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/tg/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$lipids_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(tg), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/tg/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# gluco

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$gluco_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/gluco/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$gluco_ok==1,]

vars01<-c("gluco00","gluco01","gluco02","gluco03","gluco04","gluco05","gluco06","gluco07","gluco08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("gluco")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/gluco/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$gluco_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(gluco), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/gluco/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# hb1ac

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$hb1ac_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/hb1ac/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$hb1ac_ok==1,]

vars01<-c("hb1ac00","hb1ac01","hb1ac02","hb1ac03","hb1ac04","hb1ac05","hb1ac06","hb1ac07","hb1ac08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("hb1ac")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/hb1ac/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$hb1ac_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(hb1ac), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/hb1ac/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# egfr

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$egfr_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/egfr/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$egfr_ok==1,]

vars01<-c("egfr00","egfr01","egfr02","egfr03","egfr04","egfr05","egfr06","egfr07","egfr08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("egfr")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/egfr/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$egfr_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(egfr), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/egfr/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# nlr

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$nlr_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/nlr/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$nlr_ok==1,]

vars01<-c("nlr00","nlr01","nlr02","nlr03","nlr04","nlr05","nlr06","nlr07","nlr08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("nlr")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/nlr/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$nlr_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(nlr), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/nlr/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


# plat

load("./Data/LTPA_PREDIMED2.RData")
dat$age00<-floor(dat$age00)
xxx<-dat[dat$plat_ok==1,
         c("id","age00","sexo","escolar00",
           "diabetes00","hipercol00","hipertg00",
           "hta00","tobacco00","obesity00","adobesity00","dmed00","kcal00",
           "mvltpa_cat2")]
xxx$sel<-1

mvltpa<-NULL
mvltpa<-createTable(compareGroups(mvltpa_cat2~.
                                  -id-sel,
                                  xxx, 
                                  method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                           "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                    show.n=TRUE, hide.no=0)
tab<-NULL
tab<-createTable(compareGroups(sel~.
                               -id-mvltpa_cat2,
                               xxx, 
                               method=c("sexo"=3,"escolar00"=3,"diabetes00"=3,"hipercol00"=3,
                                        "hipertg00"=3,"hta00"=3,"tobacco00"=3,"obesity00"=3,"adobesity00"=3)),
                 show.n=TRUE, hide.no=0)
tab<-cbind(tab$descr[,1],mvltpa$descr)
colnames(tab)<-c("All","MVLTPA <100","MVLTPA >100","P-value","N")
write.table(tab,file="./Outputs2/plat/Descriptive/descriptive.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2.RData")
dat<-dat[dat$plat_ok==1,]

vars01<-c("plat00","plat01","plat02","plat03","plat04","plat05","plat06","plat07","plat08")
tab<-NULL
for(i in 1:length(vars01))
{
  det1<-round(length(which(!is.na(dat[,vars01[i]])))/dim(dat)[1]*100,1)
  tab<-rbind(tab,cbind(det1))
}

tab<-t(tab)
rownames(tab)<-c("plat")
colnames(tab)<-c("Baseline","1 year","2 years","3 years","4 years","5 years","6 years","7 years","8 years")
write.table(tab,file="./Outputs2/plat/Descriptive/non_NA_values.csv",sep=";",col.names=NA)

load("./Data/LTPA_PREDIMED2_long.RData")
dat_long<-dat_long[dat_long$plat_ok==1,]
age_counts <- dat_long %>%
  mutate(age_int = floor(age)) %>%
  filter(age_int >= 60 & age_int <= 85) %>%
  group_by(age_int) %>%
  dplyr::summarise(
    across(c(plat), ~ sum(!is.na(.x)), .names = "rows_with_{.col}"),
    .groups = "drop"
  )
write.table(age_counts,file="./Outputs2/plat/Descriptive/non_NA_values_age.csv",sep=";",col.names=NA)


###########################
### MIXED LINEAR MODELS ###
###########################

setwd("D:/Artículos/Eleonora - LTPA PREDIMED")

#https://fromthebottomoftheheap.net/2021/02/02/random-effects-in-gams/


#######################
### BODY MASS INDEX ###
#######################

vars00<-c("Body mass index, kg/m²\n(predicted values, 95% CI)")
vars0x<-c("BMI (kg/m²)")
vars01<-c("bmi")
vars02<-c("bmi_ok")
vars03<-c("obesity200")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80","81","82","83","84","85")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,85,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80 | gam_predict$seg==85,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80","v85")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-lm(v85~as.factor(group),data=gam_predictx)
  
  class_g1<-c(">100 vs. <100")
  
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-intervals(mod85)[2,1]
  lo85_g1<-intervals(mod85)[2,2]
  hi85_g1<-intervals(mod85)[2,3]
  coef85_g1<-ic_guapa2(guapa(beta85_g1),guapa(lo85_g1),guapa(hi85_g1))
  pval85_g1<-pval_guapa(intervals(mod85)[2,4])
  
  plot.data <- plot.data %>%
    filter(seg >= 75) %>%
    select(seg, group0_fit, group1_fit)
  slope75_85_g0<-intervals(lm(group0_fit~seg,data=plot.data))[2,1]
  slope75_85_g1<-intervals(lm(group1_fit~seg,data=plot.data))[2,1]
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  tab3<-rbind(tab3,cbind(slope75_85_g0,slope75_85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,85,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80 | gam_predict$seg==85,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80","v85")
  
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-lm(v85~as.factor(group),data=gam_predictx)
  
  class_g1<-c(">100 vs. <100")
  
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-intervals(mod85)[2,1]
  lo85_g1<-intervals(mod85)[2,2]
  hi85_g1<-intervals(mod85)[2,3]
  coef85_g1<-ic_guapa2(guapa(beta85_g1),guapa(lo85_g1),guapa(hi85_g1))
  pval85_g1<-pval_guapa(intervals(mod85)[2,4])
  
  plot.data <- plot.data %>%
    filter(seg >= 75) %>%
    select(seg, group0_fit, group1_fit)
  slope75_85_g0<-intervals(lm(group0_fit~seg,data=plot.data))[2,1]
  slope75_85_g1<-intervals(lm(group1_fit~seg,data=plot.data))[2,1]
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  tab3<-rbind(tab3,cbind(slope75_85_g0,slope75_85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,85,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80 | gam_predict$seg==85,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80","v85")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-lm(v85~as.factor(group),data=gam_predictx)
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-intervals(mod85)[2,1]
  lo85_g1<-intervals(mod85)[2,2]
  hi85_g1<-intervals(mod85)[2,3]
  coef85_g1<-ic_guapa2(guapa(beta85_g1),guapa(lo85_g1),guapa(hi85_g1))
  pval85_g1<-pval_guapa(intervals(mod85)[2,4])
  
  plot.data <- plot.data %>%
    filter(seg >= 75) %>%
    select(seg, group0_fit, group1_fit)
  slope75_85_g0<-intervals(lm(group0_fit~seg,data=plot.data))[2,1]
  slope75_85_g1<-intervals(lm(group1_fit~seg,data=plot.data))[2,1]
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  tab3<-rbind(tab3,cbind(slope75_85_g0,slope75_85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,85,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80 | gam_predict$seg==85,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80","v85")
  
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-lm(v85~as.factor(group),data=gam_predictx)
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-intervals(mod85)[2,1]
  lo85_g1<-intervals(mod85)[2,2]
  hi85_g1<-intervals(mod85)[2,3]
  coef85_g1<-ic_guapa2(guapa(beta85_g1),guapa(lo85_g1),guapa(hi85_g1))
  pval85_g1<-pval_guapa(intervals(mod85)[2,4])
  
  plot.data <- plot.data %>%
    filter(seg >= 75) %>%
    select(seg, group0_fit, group1_fit)
  slope75_85_g0<-intervals(lm(group0_fit~seg,data=plot.data))[2,1]
  slope75_85_g1<-intervals(lm(group1_fit~seg,data=plot.data))[2,1]
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  tab3<-rbind(tab3,cbind(slope75_85_g0,slope75_85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,85,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80 | gam_predict$seg==85,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80","v85")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-lm(v85~as.factor(group),data=gam_predictx)
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-intervals(mod85)[2,1]
  lo85_g1<-intervals(mod85)[2,2]
  hi85_g1<-intervals(mod85)[2,3]
  coef85_g1<-ic_guapa2(guapa(beta85_g1),guapa(lo85_g1),guapa(hi85_g1))
  pval85_g1<-pval_guapa(intervals(mod85)[2,4])
  
  plot.data <- plot.data %>%
    filter(seg >= 75) %>%
    select(seg, group0_fit, group1_fit)
  slope75_85_g0<-intervals(lm(group0_fit~seg,data=plot.data))[2,1]
  slope75_85_g1<-intervals(lm(group1_fit~seg,data=plot.data))[2,1]
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  tab3<-rbind(tab3,cbind(slope75_85_g0,slope75_85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,85,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80 | gam_predict$seg==85,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80","v85")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-lm(v85~as.factor(group),data=gam_predictx)
  
  class_g1<-c(">100 vs. <100")
  
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-intervals(mod85)[2,1]
  lo85_g1<-intervals(mod85)[2,2]
  hi85_g1<-intervals(mod85)[2,3]
  coef85_g1<-ic_guapa2(guapa(beta85_g1),guapa(lo85_g1),guapa(hi85_g1))
  pval85_g1<-pval_guapa(intervals(mod85)[2,4])
  
  plot.data <- plot.data %>%
    filter(seg >= 75) %>%
    select(seg, group0_fit, group1_fit)
  slope75_85_g0<-intervals(lm(group0_fit~seg,data=plot.data))[2,1]
  slope75_85_g1<-intervals(lm(group1_fit~seg,data=plot.data))[2,1]
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  tab3<-rbind(tab3,cbind(slope75_85_g0,slope75_85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab3)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/slopes.csv",sep="")
  write.table(tab3,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}


###########################
### WAIST CIRCUMFERENCE ###
###########################

vars00<-c("Waist circumference, cm\n(predicted values, 95% CI)",
          "Waist-to-height ratio,\n(predicted values, 95% CI)")
vars0x<-c("WC (cm)","WHtR (ratio)")
vars01<-c("wc","whtr")
vars02<-c("wc_ok","wc_ok")
vars03<-c("adobesity00","c_adip00")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}


###################
### CHOLESTEROL ###
###################

vars00<-c("Total cholesterol, mg/dL\n(predicted values, 95% CI)",
          "HDL cholesterol, mg/dL\n(predicted values, 95% CI)",
          "LDL cholesterol, mg/dL\n(predicted values, 95% CI)",
          "LDL-C/HDL-C ratio\n(predicted values, 95% CI)")
vars0x<-c("Total C (mg/dL)","HDL-C (mg/dL)","LDL-C (mg/dL)","LDL-C/HDL-C")
vars01<-c("tc","hdlc","ldlc","ldlc_hdlc")
vars02<-c("lipids_ok","lipids_ok","lipids_ok","lipids_ok")
vars03<-c("hipercol00","hdl_lo_00","ldl_hi130_00","ldl_hdl_hi3_00")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","f_chol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$f_chol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","f_chol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$f_chol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","f_chol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$f_chol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}


#####################
### TRIGLYCERIDES ###
#####################

vars00<-c("Triglycerides, mg/dL\n(predicted values, 95% CI)")
vars0x<-c("TG (mg/dL)")
vars01<-c("tg")
vars02<-c("lipids_ok")
vars03<-c("hipertg00")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","f_tg00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","hipertg","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$f_tg00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","hipertg","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","f_tg00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","hipertg","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$f_tg00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","hipertg","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","f_tg00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","hipertg","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+hipertg+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$f_tg00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","hipertg","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}


######################
### BLOOD PRESSURE ###
######################

vars00<-c("Systolic blood pressure, mmHg\n(predicted values, 95% CI)",
          "Diastolic blood pressure, mmHg\n(predicted values, 95% CI)")
vars0x<-c("SBP (mmHg)","DBP (mmHg)")
vars01<-c("sbp","dbp")
vars02<-c("sbp_ok","dbp_ok")
vars03<-c("hta00","hta00")
vars06<-c("diabetes00","diabetes00")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","f_hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$f_hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    #annotate("text", x=max(plot.data$seg)*0.95, y=maxx, label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","f_hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$f_hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","f_hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$f_hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   vars06[i],"hipercol00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "covar","hipercol","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$hipercol00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","covar","hipercol","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   vars06[i],"hipercol00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "covar","hipercol","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$hipercol00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","covar","hipercol","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   vars06[i],"hipercol00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "covar","hipercol00","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +covar+hipercol+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$hipercol00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","covar","hipercol","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}


###############
### GLUCOSE ###
###############

vars00<-c("Fasting glucose, mg/dL\n(predicted values, 95% CI)")
vars0x<-c("Glucose (mg/dL)")
vars01<-c("gluco")
vars02<-c("gluco_ok")
vars03<-c("diabetes00")
vars06<-c("hta00")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "f_gluco00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$f_gluco00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "f_gluco00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$f_gluco00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "f_gluco00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$f_gluco00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   vars06[i],"tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "covar","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","covar","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   vars06[i],"tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "covar","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","covar","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    #annotate("text", x=max(plot.data$seg)*0.95, y=maxx, label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   vars06[i],"tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "covar","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +covar+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","covar","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}


#############
### Hb1Ac ###
#############

vars00<-c("Glycated hemoglobin, %\n(predicted values, 95% CI)")
vars0x<-c("Hb1Ac (%)")
vars01<-c("hb1ac")
vars02<-c("hb1ac_ok")
vars03<-c("diabetes00")
vars06<-c("hta00")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & !is.na(dat_long$gluco_basal),]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "f_gluco00","gluco_basal","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","gluco","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$f_gluco00,dat_long$gluco_basal,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","gluco","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & !is.na(dat_long$gluco_basal) & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "f_gluco00","gluco_basal","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","gluco","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$f_gluco00,dat_long$gluco_basal,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","gluco","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & !is.na(dat_long$gluco_basal) & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "f_gluco00","gluco_basal","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","gluco","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+gluco+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$f_gluco00,dat_long$gluco_basal,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","gluco","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & !is.na(dat_long$gluco_basal) & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   vars06[i],"gluco_basal","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "covar","gluco","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$gluco_basal,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","covar","gluco","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & !is.na(dat_long$gluco_basal) & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   vars06[i],"gluco_basal","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "covar","gluco","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$gluco_basal,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","covar","gluco","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    #annotate("text", x=max(plot.data$seg)*0.95, y=maxx, label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & !is.na(dat_long$gluco_basal) & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   vars06[i],"gluco_basal","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "covar","gluco","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +covar+gluco+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long[,vars06[i]],dat_long$gluco_basal,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","covar","gluco","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}


########################
### OTHER BIOMARKERS ###
########################

vars00<-c("Estimated glomerular filtration rate, mL/min·1.73 m²\n(predicted values, 95% CI)",
          "Neutrophil-to-lymphocyte ratio\n(predicted values, 95% CI)",
          "Platelets, 10⁹/L\n(predicted values, 95% CI)")
vars0x<-c("eGFR (mL/min·1.73 m²)","N-L ratio (mg/dL)","Platelets (10⁹/L)")
vars01<-c("egfr","nlr","plat")
vars02<-c("egfr_ok","nlr_ok","plat_ok")
vars03<-c("ckd_00","nlr_median00","plat_median00")

vars04<-c("60","61","62","63","64",
          "65","66","67","68","69","70","71","72","73","74",
          "75","76","77","78","79","80")

for(i in 1:length(vars01))
  
{
  tab1<-NULL
  tab2<-NULL
  tab3<-NULL
  tab4<-NULL
  tab5<-NULL
  tab6<-NULL
  tab7<-NULL
  tab8<-NULL
  
  # ALL PARTICIPANTS #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab1<-rbind(tab1,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # ONLY WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab4<-rbind(tab4,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # MEN ONLY #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is BMI different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of BMI over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab5<-rbind(tab5,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - ALL #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","sexo","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","sexo","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+sexo+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$sexo,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","sexo","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_all.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab6<-rbind(tab6,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - WOMEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==1,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_women.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab7<-rbind(tab7,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  # PARTICIPANTS WITH THE CONDITION - MEN #
  load("./Data/LTPA_PREDIMED2_long.RData")
  dat_long<-dat_long[!is.na(dat_long[,vars01[i]]) & dat_long[,vars02[i]]==1 & dat_long[,vars03[i]]==1 & dat_long$sexo==0,]
  
  xxx<-dat_long[,c("id",vars01[i],"mvltpa_cat2","age","escolar00","grup_int2",
                   "diabetes00","hipercol00","hta00","tobacco200","bmi00","dmed00","kcal00")]
  names(xxx)<-c("id","variable","group","seg","escolar","grup_int",
                "diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  xxx$id2<-as.factor(xxx$id)
  xxx$seg<-as.numeric(xxx$seg)
  xxx$dmed<-as.numeric(xxx$dmed)
  
  # Non-linear age is better than linear age?
  mod_lin<-lme(variable~seg*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Is the risk factor different in the groups of MVLTPA?
  mod_par<-lme(variable~bs(seg, df=4)+group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  # Our model: Non-linear mixed model
  mod_gam<-lme(variable~bs(seg, df=4)*group+escolar+grup_int
               +diabetes+hipercol+hta+tabaco+bmi+dmed+kcal, 
               random = ~1 | id2, 
               correlation = corCAR1(form = ~seg | id2), 
               control = lmeControl(opt = "nlminb", msMaxIter = 200, niterEM = 50), 
               data=xxx,
               method='REML',
               na.action=na.exclude)
  
  pval_group<-pval_guapa(summary(mod_gam)$tTable[6,5])
  pval_time_group<-pval_guapa(lrtest(mod_par,mod_gam)[2,5])
  pval_nonlin_time<-pval_guapa(lrtest(mod_lin,mod_gam)[2,5])
  
  # Estimation of predicted values of the risk factor over time in the four non-linear equations
  gam_predict<-expand.grid(group=factor(c(0,1)),
                           seg=seq(60,80,by=1),
                           id=unique(dat_long$id))
  
  xxx<-as.data.frame(unique(cbind(dat_long$id,dat_long$mvltpa_cat2,dat_long$escolar00,dat_long$grup_int2,
                                  dat_long$diabetes00,dat_long$hipercol00,dat_long$hta00,dat_long$tobacco200,dat_long$bmi00,dat_long$dmed00,dat_long$kcal00)))
  vars_needed<-c("id","group_ok","escolar","grup_int","diabetes","hipercol","hta","tabaco","bmi","dmed","kcal")
  names(xxx)<-vars_needed
  xxx$dmed<-as.numeric(xxx$dmed)
  
  gam_predict<-merge2(gam_predict,xxx,by.id=c("id"),all.x=TRUE,sort=FALSE)
  gam_predict$group_ok<-as.numeric(gam_predict$group_ok)-1
  gam_predict$id2<-as.factor(gam_predict$id)
  gam_predict<-tidyr::drop_na(gam_predict, all_of(vars_needed))
  
  gam_predict<-gam_predict %>% 
    mutate(fit=predict(mod_gam,gam_predict,level=0,type="response"))
  
  gam_predict<-gam_predict[gam_predict$group==gam_predict$group_ok,]
  gam_predict0<-gam_predict[gam_predict$group==0,c("id","seg","fit")]
  gam_predict1<-gam_predict[gam_predict$group==1,c("id","seg","fit")]
  
  group0<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict0[gam_predict0$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group0<-as.data.frame(rbind(group0,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group0)<-c("seg","group0_fit","group0_lo","group0_hi")
  
  group1<-NULL
  for(j in 1:length(vars04))
  {
    xxx<-na.omit(gam_predict1[gam_predict1$seg==vars04[j],])
    meanx<-mean(xxx$fit)
    stdex<-se(xxx$fit)
    group1<-as.data.frame(rbind(group1,cbind(as.numeric(vars04[j]),meanx,meanx-z*stdex,meanx+z*stdex)))
  }
  names(group1)<-c("seg","group1_fit","group1_lo","group1_hi")
  
  plot.data<-merge2(group0,group1,by.id=c("seg"),all.x=TRUE,sort=FALSE)
  figure<-ggplot(data=plot.data, aes_string(x='seg', y='group0_fit')) + 
    geom_ribbon(aes_string(ymin='group0_lo', ymax='group0_hi'), alpha=0.25, fill="#2b2b2b") +
    geom_line(aes_string(x='seg', y='group0_fit'), color='#2b2b2b') + 
    geom_ribbon(aes_string(ymin='group1_lo', ymax='group1_hi'), alpha=0.25, fill="#0072B2") +
    geom_line(aes_string(x='seg', y='group1_fit'), color='#0072B2') +
    theme_bw() +
    scale_x_continuous(expand = expansion(mult = c(0, 0.005))) +
    labs(x=c("Follow-up time (years)"),y=vars00[i]) +
    theme(axis.title.x = element_text(vjust=0.5, size=18, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=18, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/",vars01[i],"_cond_men.jpg",sep="")
  ggsave(filename=namefile,dpi=1200)
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  gam_predictx<-spread(gam_predict[gam_predict$seg==60 | gam_predict$seg==65 | gam_predict$seg==70 | gam_predict$seg==75 | gam_predict$seg==80,
                                   c("id","seg","fit","group")], seg, fit)
  names(gam_predictx)<-c("id","group","v60","v65","v70","v75","v80")
  
  mod60<-lm(v60~as.factor(group),data=gam_predictx)
  mod65<-lm(v65~as.factor(group),data=gam_predictx)
  mod70<-lm(v70~as.factor(group),data=gam_predictx)
  mod75<-lm(v75~as.factor(group),data=gam_predictx)
  mod80<-lm(v80~as.factor(group),data=gam_predictx)
  mod85<-NA
  
  class_g1<-c(">100 vs. <100")
  beta60_g1<-intervals(mod60)[2,1]
  lo60_g1<-intervals(mod60)[2,2]
  hi60_g1<-intervals(mod60)[2,3]
  coef60_g1<-ic_guapa2(guapa(beta60_g1),guapa(lo60_g1),guapa(hi60_g1))
  pval60_g1<-pval_guapa(intervals(mod60)[2,4])
  beta65_g1<-intervals(mod65)[2,1]
  lo65_g1<-intervals(mod65)[2,2]
  hi65_g1<-intervals(mod65)[2,3]
  coef65_g1<-ic_guapa2(guapa(beta65_g1),guapa(lo65_g1),guapa(hi65_g1))
  pval65_g1<-pval_guapa(intervals(mod65)[2,4])
  beta70_g1<-intervals(mod70)[2,1]
  lo70_g1<-intervals(mod70)[2,2]
  hi70_g1<-intervals(mod70)[2,3]
  coef70_g1<-ic_guapa2(guapa(beta70_g1),guapa(lo70_g1),guapa(hi70_g1))
  pval70_g1<-pval_guapa(intervals(mod70)[2,4])
  beta75_g1<-intervals(mod75)[2,1]
  lo75_g1<-intervals(mod75)[2,2]
  hi75_g1<-intervals(mod75)[2,3]
  coef75_g1<-ic_guapa2(guapa(beta75_g1),guapa(lo75_g1),guapa(hi75_g1))
  pval75_g1<-pval_guapa(intervals(mod75)[2,4])
  beta80_g1<-intervals(mod80)[2,1]
  lo80_g1<-intervals(mod80)[2,2]
  hi80_g1<-intervals(mod80)[2,3]
  coef80_g1<-ic_guapa2(guapa(beta80_g1),guapa(lo80_g1),guapa(hi80_g1))
  pval80_g1<-pval_guapa(intervals(mod80)[2,4])
  beta85_g1<-NA
  lo85_g1<-NA
  hi85_g1<-NA
  coef85_g1<-NA
  pval85_g1<-NA
  
  tab8<-rbind(tab8,cbind(class_g1,beta60_g1,lo60_g1,hi60_g1,beta65_g1,lo65_g1,hi65_g1,
                         beta70_g1,lo70_g1,hi70_g1,beta75_g1,lo75_g1,hi75_g1,beta80_g1,lo80_g1,hi80_g1,beta85_g1,lo85_g1,hi85_g1))
  tab2<-rbind(tab2,cbind(class_g1,pval_group,pval_time_group,pval_nonlin_time,coef60_g1,pval60_g1,coef65_g1,pval65_g1,
                         coef70_g1,pval70_g1,coef75_g1,pval75_g1,coef80_g1,pval80_g1,coef85_g1,pval85_g1))
  
  
  rownames(tab1)<-c(vars0x[i])
  rownames(tab2)<-c("all","women","men","cond_all","cond_women","cond_men")
  rownames(tab4)<-c(vars0x[i])
  rownames(tab5)<-c(vars0x[i])
  rownames(tab6)<-c(vars0x[i])
  rownames(tab7)<-c(vars0x[i])
  rownames(tab8)<-c(vars0x[i])
  
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_all.csv",sep="")
  write.table(tab1,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/repeated.csv",sep="")
  write.table(tab2,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_women.csv",sep="")
  write.table(tab4,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_men.csv",sep="")
  write.table(tab5,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_all.csv",sep="")
  write.table(tab6,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_women.csv",sep="")
  write.table(tab7,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots_cond_men.csv",sep="")
  write.table(tab8,file=namefile,sep=";",col.names=NA)
}



### FOREST PLOTS OF DIFFERENCES IN PREDICTED MEANS ###
######################################################

# Syntax to create the file that the forest plot syntax can use

setwd("D:/Artículos/Eleonora - LTPA PREDIMED")

vars01<-c("bmi","bmi","bmi","bmi","bmi","bmi",
          "wc","wc","wc","wc","wc","wc",
          "whtr","whtr","whtr","whtr","whtr","whtr",
          "sbp","sbp","sbp","sbp","sbp","sbp",
          "dbp","dbp","dbp","dbp","dbp","dbp",
          "tc","tc","tc","tc","tc","tc",
          "hdlc","hdlc","hdlc","hdlc","hdlc","hdlc",
          "ldlc","ldlc","ldlc","ldlc","ldlc","ldlc",
          "ldlc_hdlc","ldlc_hdlc","ldlc_hdlc","ldlc_hdlc","ldlc_hdlc","ldlc_hdlc",
          "tg","tg","tg","tg","tg","tg",
          "gluco","gluco","gluco","gluco","gluco","gluco",
          "hb1ac","hb1ac","hb1ac","hb1ac","hb1ac","hb1ac",
          "egfr","egfr","egfr","egfr","egfr","egfr",
          "nlr","nlr","nlr","nlr","nlr","nlr",
          "plat","plat","plat","plat","plat","plat")
vars02<-c("_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men",
          "_all","_women","_men","_cond_all","_cond_women","_cond_men")
vars03<-c("90","90","90","90","90","90",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85",
          "85","85","85","85","85","85")

for(i in 1:length(vars01))
  
{
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/forestplots",vars02[i],".csv",sep="")
  dat<-read.csv2(namefile,header=TRUE,sep=";",dec=".")
  tabx<-dat
  tab<-NULL
  tab<-rbind(cbind(c(60),rbind(tab,cbind(tabx$beta60_g1,tabx$lo60_g1,tabx$hi60_g1)),tabx$X,tabx$class_g1),
             cbind(c(65),rbind(tab,cbind(tabx$beta65_g1,tabx$lo65_g1,tabx$hi65_g1)),tabx$X,tabx$class_g1),
             cbind(c(70),rbind(tab,cbind(tabx$beta70_g1,tabx$lo70_g1,tabx$hi70_g1)),tabx$X,tabx$class_g1),
             cbind(c(75),rbind(tab,cbind(tabx$beta75_g1,tabx$lo75_g1,tabx$hi75_g1)),tabx$X,tabx$class_g1),
             cbind(c(80),rbind(tab,cbind(tabx$beta80_g1,tabx$lo80_g1,tabx$hi80_g1)),tabx$X,tabx$class_g1),
             cbind(c(85),rbind(tab,cbind(tabx$beta85_g1,tabx$lo85_g1,tabx$hi85_g1)),tabx$X,tabx$class_g1))
  colnames(tab)<-c("year","pred_diff","lci","uci","out","class")
  tab<-as.data.frame(tab)
  tab$pred_diff<-as.numeric(tab$pred_diff)
  tab$lci<-as.numeric(tab$lci)
  tab$uci<-as.numeric(tab$uci)
  tab$coef<-ic_guapa2(guapa(tab$pred_diff),guapa(tab$lci),guapa(tab$uci))
  tab$coef<-with(tab,ifelse(coef=="NA (NA to NA)",NA,coef))
  tab$class<-with(tab,ifelse(class==">100 vs. <100","1",NA))
  tab$class<-as.factor(tab$class)
  tab<-subset(tab, year!=vars03[i])
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/f",vars02[i],".csv",sep="")
  write.table(tab,file=namefile,sep=";",col.names=NA)
}

# Syntax to generate the individual forest plots #

for(i in 1:length(vars01))
{
  namefile <- paste("./Outputs2/",vars01[i],"/Repeated/f",vars02[i],".csv",sep="")
  dat <- read.csv2(namefile,header=TRUE,sep=";",dec=".")
  dat$class <- as.factor(dat$class)
  label <- dat$out[1]
  
  dat$year_f <- factor(dat$year)
  dodge <- position_dodge(width = 0.7)
  figure <- ggplot(dat, aes(x = year_f, colour = class, group = class)) +
    geom_hline(yintercept = 0, linetype = 2) +
    geom_point(aes(y = pred_diff), shape = 15, size = 3, position = dodge) +
    geom_linerange(aes(ymin = lci, ymax = uci, y = pred_diff), size = 0.8, position = dodge) +
    # ── Place coefficients just outside the right edge; don't let them create legend entries
    geom_text(aes(y = Inf, label = coef), position = dodge,
              vjust = 0.5, hjust = 0, size = 5, show.legend = FALSE) +
    # ── Allow drawing outside the panel
    coord_flip(clip = "off") +
    scale_colour_manual(name = "",
                        values = c('#0072B2'),
                        labels = c(">100 vs. <100 METs-min/d")) +
    scale_y_continuous(expand = expansion(mult = c(0.1, 0.2))) +
    xlab("Follow-up time (years)") +
    ylab(paste0("Inter-group difference,\n", label)) +
    theme_minimal() +
    theme(
      panel.grid = element_blank(),
      axis.line = element_line(colour = "black"),
      axis.text = element_text(size = 15),
      axis.title = element_text(size = 15, face = "bold"),
      legend.position = "bottom",
      legend.direction = "horizontal",
      legend.text = element_text(size = 10),
      plot.margin = margin(5, 160, 5, 2, "pt")
    )
  
  # ── Make the image wider so the outside labels never get clipped (non-square OK)
  namefile2 <- paste("./Outputs2/",vars01[i],"/Repeated/forest_",vars01[i],vars02[i],".jpg",sep="")
  ggsave(filename = namefile2, units = "px",
         width = 8400, height = 4200,  # wider than tall
         dpi = 1200, bg = "white")
  figure
}


# Syntax to generate a combined forest plot

vars01<-c("bmi","wc","whtr","sbp","dbp",
          "tc","hdlc","ldlc","ldlc_hdlc","tg",
          "gluco","hb1ac","egfr","nlr","plat")
vars02<-c(-3.5,5,-3.5,3,2.5,
          2,3,2.5,3,6,
          2,3,2.25,4,3.5)
vars03<-c("Baseline obesity, all","Baseline abd. ob., all","Baseline adip., all",
          "Baseline hyperten., all","Baseline hyperten., all","Baseline hyperchol., all",
          "Baseline low HDL-C, all","Baseline ≥130 mg/dL, all","Baseline ≥3, all",
          "Baseline ≥150 mg/dL, all","Baseline ≥126 mg/dL, all","Baseline ≥6.5%, all",
          "Baseline CKD, all","Baseline >median, all","Baseline >median, all")
vars04<-c("Baseline obesity, women","Baseline abd. ob., women","Baseline adip., women",
          "Baseline hyperten., women","Baseline hyperten., women","Baseline hyperchol., women",
          "Baseline low HDL-C, women","Baseline ≥130 mg/dL, women","Baseline ≥3, women",
          "Baseline ≥150 mg/dL, women","Baseline ≥126 mg/dL, women","Baseline ≥6.5%, women",
          "Baseline CKD, women","Baseline >median, women","Baseline >median, women")
vars05<-c("Baseline obesity, men","Baseline abd. ob., men","Baseline adip., men",
          "Baseline hyperten., men","Baseline hyperten., men","Baseline hyperchol., men",
          "Baseline low HDL-C, men","Baseline ≥130 mg/dL, men","Baseline ≥3, men",
          "Baseline ≥150 mg/dL, men","Baseline ≥126 mg/dL, men","Baseline ≥6.5%, men",
          "Baseline CKD, men","Baseline >median, men","Baseline >median, men")

for(i in 1:length(vars01))
{
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/f_all.csv",sep="")
  tab1<-read.csv2(namefile,header=TRUE,sep=";",dec=".")[,2:8]
  tab1$class<-6
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/f_women.csv",sep="")
  tab2<-read.csv2(namefile,header=TRUE,sep=";",dec=".")[,2:8]
  tab2$class<-5
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/f_men.csv",sep="")
  tab3<-read.csv2(namefile,header=TRUE,sep=";",dec=".")[,2:8]
  tab3$class<-4
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/f_cond_all.csv",sep="")
  tab4<-read.csv2(namefile,header=TRUE,sep=";",dec=".")[,2:8]
  tab4$class<-3
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/f_cond_women.csv",sep="")
  tab5<-read.csv2(namefile,header=TRUE,sep=";",dec=".")[,2:8]
  tab5$class<-2
  namefile<-paste("./Outputs2/",vars01[i],"/Repeated/f_cond_men.csv",sep="")
  tab6<-read.csv2(namefile,header=TRUE,sep=";",dec=".")[,2:8]
  tab6$class<-1
  dat<-rbind(tab1,tab2,tab3,tab4,tab5,tab6)
  
  dat$class<-as.factor(dat$class)
  label<-dat$out[1]
  dat$year<-factor(dat$year)
  pd<-position_dodge(width=0.7)
  
  figure<-ggplot() +
    geom_hline(yintercept=0, linetype=2) +
    geom_point(data=dat, aes(x=year, y=pred_diff, col=class), size = 2.5, shape = 15, position=pd) +
    geom_linerange(data=dat, aes(x=year, y=pred_diff, ymin=lci, ymax=uci, col=class), size=0.6, position=pd) +
    coord_flip() +
    geom_text(data=dat, size=4, aes(y=max(uci)*vars02[i], x=year, label=coef, hjust='inward', col=class), position=pd) +
    scale_x_discrete(breaks = levels(dat$year)) +
    xlab("Age (years)") +
    ylab(paste("Inter-group diff., ",label,sep="")) +
    theme_minimal() +
    scale_colour_manual(name="",
                        values=c('#D55E00','#de026e','#5833ff','#117733','#882255','black'),
                        labels=c(vars05[i],vars04[i],vars03[i],"Men","Women","All participants")) +
    theme(panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          panel.background = element_blank(),
          axis.line=element_line(colour = "black"),
          axis.text.y=element_text(size=12),
          axis.text.x=element_text(size=12),
          axis.ticks.y=element_line(),
          axis.ticks.x=element_line(),
          axis.title.x=element_text(size=15, face="bold"),
          axis.title.y=element_text(size=15, face="bold"),
          legend.position="right",
          legend.title=element_blank(),
          legend.text=element_text(size=10),
          legend.justification="center")
  
  namefile2 <- paste("./Outputs2/",vars01[i],"/Repeated/forest_",vars01[i],".jpg",sep="")
  ggsave(filename = namefile2, units = "px", width = 8400, height = 8400, dpi = 1200, bg = "white")
  figure
}


#########################
### SURVIVAL ANALYSES ###
#########################

# BLOOD PRESSURE, LIPID PROFILE, GLUCOSE #

load("./Data/LTPA_PREDIMED2.RData")
dat$covar<-1
dat$mvltpalong2<-dat$mvltpalong/25 # We express differences per 25 METs-min/day (175 METs-min/week)

vars00<-c("sbp","sbp",
          "ldlc","ldlc","hdlc","ldlc",
          "gluco","gluco","hb1ac")
varsxx<-c("bp_hi","f_hta",
          "ldl_hi130","ldl_hi160","hdl_lo","f_chol",
          "gluco_hi126","f_gluco","hb1ac_hi")
vars01<-NULL
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-NULL
vars08<-c("Marginal cumulative incidence\nof high blood pressure",
          "Marginal cumulative incidence\nof antihypertensive drug initiation",
          "Marginal cumulative incidence\nof LDL cholesterol ≥130 mg/dL",
          "Marginal cumulative incidence\nof LDL cholesterol ≥160 mg/dL",
          "Marginal cumulative incidence\nof low HDL cholesterol",
          "Marginal cumulative incidence\nof cholesterol-lowering drug initiation",
          "Marginal cumulative incidence\nof glucose ≥126 mg/dL",
          "Marginal cumulative incidence\nof glucose-lowering drug initiation",
          "Marginal cumulative incidence\nof Hb1Ac ≥6.5%")
vars09<-c("Onset of high blood pressure",
          "Antihypertensive drug initiation",
          "Onset of LDL cholesterol ≥130 mg/dL",
          "Onset of LDL cholesterol ≥160 mg/dL",
          "Onset of low HDL cholesterol",
          "Cholesterol-lowering drug initiation",
          "Onset of glucose ≥126 mg/dL",
          "Glucose-lowering drug initiation",
          "Onset of Hb1Ac ≥6.5%")
vars10<-c("sbp_ok","sbp_ok","lipids_ok","lipids_ok",
          "lipids_ok","lipids_ok","gluco_ok","gluco_ok","hb1ac_ok")
vars11<-c("diabetes00","diabetes00","diabetes00","diabetes00",
          "diabetes00","diabetes00","f_gluco00","gluco00","gluco00")
vars12<-c("hipercol00","hipercol00","f_chol00","f_chol00",
          "f_chol00","tc00","hipercol00","hipercol00","hipercol00")
vars13<-c("f_hta00","sbp00","hta00","hta00",
          "hta00","hta00","hta00","hta00","hta00")
vars14<-c(150,150,150,150,150,150,150,150,150) # Most beneficial MVLTPA range (a posteriori)
vars15<-c(80,80,80,80,80,80,80,80,80) # Maximum age to start the follow-up


for(i in 1:length(varsxx))
{
  vars01<-c(vars01,paste(varsxx[i],"_d",sep=""))
  vars03<-c(vars03,paste(varsxx[i],"_inicio",sep=""))
  vars05<-c(vars05,paste(varsxx[i],"_seg",sep=""))
}

for(i in 1:length(vars01))
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars04<-c(vars04,paste(vars01[i],"_when",sep=""))
  vars06<-c(vars06,paste("to",vars01[i],"_left",sep=""))
  vars07<-c(vars07,paste("to",vars01[i],"_right",sep=""))
}

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,(dat[,vars06[i]]+dat[,vars07[i]])/2,dat[,vars02[i]]))
}


for(i in 1:length(vars01))
  
{ 
  tab<-NULL
  tab_ok<-NULL
  
  labelok<-vars08[i]
  datx<-dat[dat[,vars10[i]]==1,]
  sample_orig<-dim(datx)[1]
  outliers<-length(which(datx$mvltpalong>600))
  datx<-datx[datx$mvltpalong<=600,]
  excl_basal<-length(which(datx[,vars03[i]]==1))
  datx<-datx[datx[,vars03[i]]==0,]
  samplesize<-dim(datx)[1]
  datx$xxx<-datx[, vars01[i]]
  datx$aaa<-datx[, vars11[i]]
  datx$bbb<-datx[, vars12[i]]
  datx$ccc<-datx[, vars13[i]]
  datx$start_age<-datx$age00
  datx$stop_age<-datx$age00+(datx[,vars02[i]]/365.25)
  
  median_time<-ic_guapa(guapa(summary((datx[,vars02[i]]/365.25))[3]),guapa(summary((datx[,vars02[i]]/365.25))[2]),guapa(summary((datx[,vars02[i]]/365.25))[5]))
  
  # KAPLAN-MEIER CURVES #
  
  # ALL PARTICIPANTS #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = dat2,
    ties = "efron")
  
  coef<-paste("≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc
  wt <- weightit(formula=ps_formula, data=dat2, method="ps", estimand="ATE", stabilize=TRUE)
  dat2$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=dat2, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = vars08[i],
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_all_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  # ONLY WOMEN #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  daty<-dat2[dat2$sexo==1,]
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = daty,
    ties = "efron")
  
  coef<-paste("Only female individuals,\n≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc
  wt <- weightit(formula=ps_formula, data=daty, method="ps", estimand="ATE", stabilize=TRUE)
  daty$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=daty, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = paste(vars08[i]," (women)",sep=""),
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_women_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  # ONLY MEN #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  daty<-dat2[dat2$sexo==0,]
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = daty,
    ties = "efron")
  
  coef<-paste("Only male individuals,\n≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc
  wt <- weightit(formula=ps_formula, data=daty, method="ps", estimand="ATE", stabilize=TRUE)
  daty$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=daty, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = paste(vars08[i]," (men)",sep=""),
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_men_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  
  # SURVIVAL ANALYSES #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = dat2,
    ties = "efron")
  
  hr_long_cont<-intervals(mod02)[1,1]
  ic95a_long_cont<-intervals(mod02)[1,2]
  ic95b_long_cont<-intervals(mod02)[1,3]
  pval_long_cont<-intervals(mod02)[1,4]
  pval_long_cont_ex<-intervals(mod02)[1,4]
  hr_long_cont_ok<-guapa(hr_long_cont)
  ic95a_long_cont_ok<-guapa(ic95a_long_cont)
  ic95b_long_cont_ok<-guapa(ic95b_long_cont)
  coef_long_cont<-ic_guapa2(hr_long_cont_ok,ic95a_long_cont_ok,ic95b_long_cont_ok)
  coef_long_cont2<-coef_long_cont
  pval_long_cont<-pval_guapa(pval_long_cont)
  
  mod04 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpa_cat2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = dat2,
    ties = "efron")
  hr_long_qi<-intervals(mod04)[1,1]
  ic95a_long_qi<-intervals(mod04)[1,2]
  ic95b_long_qi<-intervals(mod04)[1,3]
  pval_long_qi<-intervals(mod04)[1,4]
  hr_long_qi_ok<-guapa(hr_long_qi)
  ic95a_long_qi_ok<-guapa(ic95a_long_qi)
  ic95b_long_qi_ok<-guapa(ic95b_long_qi)
  coef_long_qi<-ic_guapa2(hr_long_qi_ok,ic95a_long_qi_ok,ic95b_long_qi_ok)
  pval_long_qi<-pval_guapa(pval_long_qi)
  
  nval_long_ca<-length(which(dat2[,vars01[i]]==1&!is.na(dat2$mvltpalong)))
  nval_long_co<-length(which(dat2[,vars01[i]]==0&!is.na(dat2$mvltpalong)))
  nval_long_cont<-paste("'",nval_long_ca,"/",nval_long_ca+nval_long_co,sep="")
  nval_long_q<-table(dat2[,vars01[i]],by=dat2$mvltpa_cat2)
  nval_long_q1<-paste("'",nval_long_q[2,1],"/",nval_long_q[2,1]+nval_long_q[1,1],sep="")
  nval_long_q2<-paste("'",nval_long_q[2,2],"/",nval_long_q[2,2]+nval_long_q[1,2],sep="")
  
  dat3<-subset2(dat2,"dat2$mvltpalong<vars14[i]")
  modxx <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = dat3,
    ties = "efron")
  hr_long_opt<-intervals(modxx)[1,1]
  ic95a_long_opt<-intervals(modxx)[1,2]
  ic95b_long_opt<-intervals(modxx)[1,3]
  pval_long_opt<-intervals(modxx)[1,4]
  pval_long_opt_ex<-intervals(modxx)[1,4]
  hr_long_opt_ok<-guapa(hr_long_opt)
  ic95a_long_opt_ok<-guapa(ic95a_long_opt)
  ic95b_long_opt_ok<-guapa(ic95b_long_opt)
  coef_long_opt<-ic_guapa2(hr_long_opt_ok,ic95a_long_opt_ok,ic95b_long_opt_ok)
  pval_long_opt<-pval_guapa(pval_long_opt)
  
  
  # SURVIVAL SPLINES #
  
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = dat2,
    ties = "efron")
  
  p_lin<-pval_long_cont
  p_nonlin<-pval_guapa(summary(mfit)$coefficients[2,6])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  
  p_lin2<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlin2<-ifelse(p_nonlin=="<0.001"," < 0.001",
                    ifelse(p_nonlin=="<0.00001"," < 0.00001",paste(" = ",p_nonlin,sep="")))
  p_lrtest2<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data)<-c("x","yest","lci","uci")
  plot.data$coef<-ic_guapa2(guapa(plot.data$y),guapa(plot.data$lci),guapa(plot.data$uci))
  min_val<-guapa(plot.data$x[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))])
  min_coef<-plot.data$coef[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))]
  plot.datax<-plot.data[,c("x","coef")]
  plot.data$coef<-NULL
  colnames(plot.datax)<-c("mvltpa","HR")
  write.table(plot.datax,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/spline_",vars01[i],".jpg",sep="")
  labely<-paste(vars09[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("p-value for linearity",p_lin2,
             "\nHR for +25 METs-min/d:\n",coef_long_cont2,
             "\np-value for non-linearity",p_lrtest2,
             "\nHR for +25 METs-min/d (range: <",vars14[i]," METs-min/d):\n",coef_long_opt,sep="")
  
  figure<-ggplot(data=plot.data, aes_string(x=plot.data$x, y=plot.data$y)) + 
    geom_ribbon(aes_string(ymin=plot.data$lci, ymax=plot.data$uci), alpha=0.25, fill='#0072B2') +
    geom_line(aes_string(x=plot.data$x, y=plot.data$y), color='#0072B2') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of moderate-vigorous LTPA\n(METs-min/day)"),y=labely) +
    annotate("text", x=max(plot.data$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  # INTERACTION TESTS #
  
  base_sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(mvltpalong, df = 4) + as.factor(sexo) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = dat2, ties = "efron")
  sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(mvltpalong, df = 4) * as.factor(sexo) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = dat2, ties = "efron")
  p_int_sexo <- pval_guapa(lrtest(base_sexo, sexo)[2, 5])
  
  
  # INTERACTION WITH SEX - SPLINES #
  
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  datm<-subset2(dat2,"dat2$sexo==0")
  datm2<-datm[datm$mvltpalong<vars14[i],]
  
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  datf<-subset2(dat2,"dat2$sexo==1")
  datf2<-datf[datf$mvltpalong<vars14[i],]
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datm,
    ties = "efron")
  coef_m<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datm2,
    ties = "efron")
  coef_m2<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datm,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datm,
    ties = "efron")
  
  p_lin<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linm<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlinm<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_m<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_m)<-c("x","yest","lci","uci")
  plot.data_m$coef<-ic_guapa2(guapa(plot.data_m$y),guapa(plot.data_m$lci),guapa(plot.data_m$uci))
  plot.data_mx<-plot.data_m[,c("x","coef")]
  plot.data_m$coef<-NULL
  colnames(plot.data_mx)<-c("mvltpa","HR")
  write.table(plot.data_mx,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_males_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_m<-subset2(plot.data_m,"plot.data_m$uci<=3")
  #plot.data_m$class<-"1"
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datf,
    ties = "efron")
  coef_f<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datf2,
    ties = "efron")
  coef_f2<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datf,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + bbb + ccc,
    data = datf,
    ties = "efron")
  
  p_lin<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linf<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlinf<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_f<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_f)<-c("x","yest","lci","uci")
  plot.data_f$coef<-ic_guapa2(guapa(plot.data_f$y),guapa(plot.data_f$lci),guapa(plot.data_f$uci))
  plot.data_fx<-plot.data_f[,c("x","coef")]
  plot.data_f$coef<-NULL
  colnames(plot.data_fx)<-c("mvltpa","HR")
  write.table(plot.data_fx,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_females_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_f<-subset2(plot.data_f,"plot.data_f$uci<=3")
  #plot.data_m$class<-"1"
  
  plot.data<-rbind(plot.data_m,plot.data_f)
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splinesex_",vars01[i],".jpg",sep="")
  labely<-paste(vars09[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("Female individuals:",
             "\nAll MVLTPA values, HR for +25 METs-min/d: ",coef_f,
             "\nMVLTPA values <150 METs-min/d, HR for +25 METs-min/d: ",coef_f2,
             "\nMale individuals:",
             "\nAll MVLTPA values, HR for +25 METs-min/d: ",coef_m,
             "\nMVLTPA values <150 METs-min/d, HR for +25 METs-min/d: ",coef_m2)
  
  figure<-ggplot() + 
    geom_ribbon(aes(x=plot.data_m$x, y=plot.data_m$y, ymin=plot.data_m$lci, ymax=plot.data_m$uci), alpha=0.25, fill='#1065B1') +
    geom_line(aes_string(x=plot.data_m$x, y=plot.data_m$y), color='#1065B1') +
    geom_ribbon(aes(x=plot.data_f$x, y=plot.data_f$y, ymin=plot.data_f$lci, ymax=plot.data_f$uci), alpha=0.25, fill='#B31529') +
    geom_line(aes_string(x=plot.data_f$x, y=plot.data_f$y), color='#B31529') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of moderate-vigorous LTPA\n(METs-min/day)"),y=labely) +
    annotate("text", x=max(plot.data_m$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  tab_ok<-rbind(tab_ok,cbind(median_time,sample_orig,outliers,excl_basal,samplesize,
                             nval_long_cont,coef_long_cont,pval_long_cont,pval_long_cont_ex,p_lrtest,
                             nval_long_q1,nval_long_q2,coef_long_qi,pval_long_qi,
                             min_val,min_coef,labelok,
                             p_int_sexo))
  tab<-rbind(tab,cbind(median_time,sample_orig,outliers,excl_basal,samplesize,
                       nval_long_cont,hr_long_cont,ic95a_long_cont,ic95b_long_cont,pval_long_cont,
                       pval_long_cont_ex,p_lrtest,
                       nval_long_q1,nval_long_q2,hr_long_qi,ic95a_long_qi,ic95b_long_qi,pval_long_qi,
                       min_val,min_coef,labelok))
  rownames(tab)<-vars01[i]
  rownames(tab_ok)<-vars01[i]
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splinedata_",vars01[i],".csv",sep="")
  write.table(tab_ok,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splineforestplot_",vars01[i],".csv",sep="")
  write.table(tab,file=namefile,sep=";",col.names=NA)
}


# TRIGLYCERIDES AND RELATED OUTCOMES #

vars00<-c("tg","tg","tg")
varsxx<-c("tg_hi150","tg_hi200","f_tg")
vars01<-NULL
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-NULL
vars08<-c("Marginal cumulative incidence\nof triglycerides ≥150 mg/dL",
          "Marginal cumulative incidence\nof triglycerides ≥200 mg/dL",
          "Marginal cumulative incidence\nof triglyceride-lowering drug initiation")
vars09<-c("Onset of triglycerides ≥150 mg/dL",
          "Onset of triglycerides ≥200 mg/dL",
          "Triglyceride-lowering drug initiation")
vars10<-c("lipids_ok","lipids_ok","lipids_ok")
vars11<-c("f_tg00","f_tg00","tg00")
vars14<-c(150,150,150) # Most beneficial MVLTPA range (a posteriori)
vars15<-c(80,80,80) # Maximum age to start the follow-up


for(i in 1:length(varsxx))
{
  vars01<-c(vars01,paste(varsxx[i],"_d",sep=""))
  vars03<-c(vars03,paste(varsxx[i],"_inicio",sep=""))
  vars05<-c(vars05,paste(varsxx[i],"_seg",sep=""))
}

for(i in 1:length(vars01))
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars04<-c(vars04,paste(vars01[i],"_when",sep=""))
  vars06<-c(vars06,paste("to",vars01[i],"_left",sep=""))
  vars07<-c(vars07,paste("to",vars01[i],"_right",sep=""))
}

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,(dat[,vars06[i]]+dat[,vars07[i]])/2,dat[,vars02[i]]))
}

for(i in 1:length(vars01))
  
{ 
  tab<-NULL
  tab_ok<-NULL
  
  labelok<-vars08[i]
  datx<-dat[dat[,vars10[i]]==1,]
  sample_orig<-dim(datx)[1]
  outliers<-length(which(datx$mvltpalong>600))
  datx<-datx[datx$mvltpalong<=600,]
  excl_basal<-length(which(datx[,vars03[i]]==1))
  datx<-datx[datx[,vars03[i]]==0,]
  samplesize<-dim(datx)[1]
  datx$xxx<-datx[, vars01[i]]
  datx$aaa<-datx[, vars11[i]]
  datx$start_age<-datx$age00
  datx$stop_age<-datx$age00+(datx[,vars02[i]]/365.25)
  
  median_time<-ic_guapa(guapa(summary((datx[,vars02[i]]/365.25))[3]),guapa(summary((datx[,vars02[i]]/365.25))[2]),guapa(summary((datx[,vars02[i]]/365.25))[5]))
  
  # KAPLAN-MEIER CURVES #
  
  # ALL PARTICIPANTS #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  
  coef<-paste("≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00)
  wt <- weightit(formula=ps_formula, data=dat2, method="ps", estimand="ATE", stabilize=TRUE)
  dat2$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=dat2, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = vars08[i],
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_all_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  # ONLY WOMEN #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  daty<-dat2[dat2$sexo==1,]
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = daty,
    ties = "efron")
  
  coef<-paste("Only female individuals,\n≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00)
  wt <- weightit(formula=ps_formula, data=daty, method="ps", estimand="ATE", stabilize=TRUE)
  daty$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=daty, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = paste(vars08[i]," (women)",sep=""),
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_women_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  # ONLY MEN #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  daty<-dat2[dat2$sexo==0,]
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = daty,
    ties = "efron")
  
  coef<-paste("Only male individuals,\n≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00)
  wt <- weightit(formula=ps_formula, data=daty, method="ps", estimand="ATE", stabilize=TRUE)
  daty$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=daty, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = paste(vars08[i]," (men)",sep=""),
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_men_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  
  # SURVIVAL ANALYSES #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  
  hr_long_cont<-intervals(mod02)[1,1]
  ic95a_long_cont<-intervals(mod02)[1,2]
  ic95b_long_cont<-intervals(mod02)[1,3]
  pval_long_cont<-intervals(mod02)[1,4]
  pval_long_cont_ex<-intervals(mod02)[1,4]
  hr_long_cont_ok<-guapa(hr_long_cont)
  ic95a_long_cont_ok<-guapa(ic95a_long_cont)
  ic95b_long_cont_ok<-guapa(ic95b_long_cont)
  coef_long_cont<-ic_guapa2(hr_long_cont_ok,ic95a_long_cont_ok,ic95b_long_cont_ok)
  coef_long_cont2<-coef_long_cont
  pval_long_cont<-pval_guapa(pval_long_cont)
  
  mod04 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpa_cat2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  hr_long_qi<-intervals(mod04)[1,1]
  ic95a_long_qi<-intervals(mod04)[1,2]
  ic95b_long_qi<-intervals(mod04)[1,3]
  pval_long_qi<-intervals(mod04)[1,4]
  hr_long_qi_ok<-guapa(hr_long_qi)
  ic95a_long_qi_ok<-guapa(ic95a_long_qi)
  ic95b_long_qi_ok<-guapa(ic95b_long_qi)
  coef_long_qi<-ic_guapa2(hr_long_qi_ok,ic95a_long_qi_ok,ic95b_long_qi_ok)
  pval_long_qi<-pval_guapa(pval_long_qi)
  
  nval_long_ca<-length(which(dat2[,vars01[i]]==1&!is.na(dat2$mvltpalong)))
  nval_long_co<-length(which(dat2[,vars01[i]]==0&!is.na(dat2$mvltpalong)))
  nval_long_cont<-paste("'",nval_long_ca,"/",nval_long_ca+nval_long_co,sep="")
  nval_long_q<-table(dat2[,vars01[i]],by=dat2$mvltpa_cat2)
  nval_long_q1<-paste("'",nval_long_q[2,1],"/",nval_long_q[2,1]+nval_long_q[1,1],sep="")
  nval_long_q2<-paste("'",nval_long_q[2,2],"/",nval_long_q[2,2]+nval_long_q[1,2],sep="")
  
  dat3<-subset2(dat2,"dat2$mvltpalong<vars14[i]")
  modxx <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat3,
    ties = "efron")
  hr_long_opt<-intervals(modxx)[1,1]
  ic95a_long_opt<-intervals(modxx)[1,2]
  ic95b_long_opt<-intervals(modxx)[1,3]
  pval_long_opt<-intervals(modxx)[1,4]
  pval_long_opt_ex<-intervals(modxx)[1,4]
  hr_long_opt_ok<-guapa(hr_long_opt)
  ic95a_long_opt_ok<-guapa(ic95a_long_opt)
  ic95b_long_opt_ok<-guapa(ic95b_long_opt)
  coef_long_opt<-ic_guapa2(hr_long_opt_ok,ic95a_long_opt_ok,ic95b_long_opt_ok)
  pval_long_opt<-pval_guapa(pval_long_opt)
  
  
  # SURVIVAL SPLINES #
  
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  
  p_lin<-pval_long_cont
  p_nonlin<-pval_guapa(summary(mfit)$coefficients[2,6])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  
  p_lin2<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlin2<-ifelse(p_nonlin=="<0.001"," < 0.001",
                    ifelse(p_nonlin=="<0.00001"," < 0.00001",paste(" = ",p_nonlin,sep="")))
  p_lrtest2<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data)<-c("x","yest","lci","uci")
  plot.data$coef<-ic_guapa2(guapa(plot.data$y),guapa(plot.data$lci),guapa(plot.data$uci))
  min_val<-guapa(plot.data$x[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))])
  min_coef<-plot.data$coef[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))]
  plot.datax<-plot.data[,c("x","coef")]
  plot.data$coef<-NULL
  colnames(plot.datax)<-c("mvltpa","HR")
  write.table(plot.datax,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/spline_",vars01[i],".jpg",sep="")
  labely<-paste(vars09[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("p-value for linearity",p_lin2,
             "\nHR for +25 METs-min/d:\n",coef_long_cont2,
             "\np-value for non-linearity",p_lrtest2,
             "\nHR for +25 METs-min/d (range: <",vars14[i]," METs-min/d):\n",coef_long_opt,sep="")
  
  figure<-ggplot(data=plot.data, aes_string(x=plot.data$x, y=plot.data$y)) + 
    geom_ribbon(aes_string(ymin=plot.data$lci, ymax=plot.data$uci), alpha=0.25, fill='#0072B2') +
    geom_line(aes_string(x=plot.data$x, y=plot.data$y), color='#0072B2') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of moderate-vigorous LTPA\n(METs-min/day)"),y=labely) +
    annotate("text", x=max(plot.data$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  # INTERACTION TESTS #
  
  base_sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(mvltpalong, df = 4) + as.factor(sexo) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2, ties = "efron")
  sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(mvltpalong, df = 4) * as.factor(sexo) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2, ties = "efron")
  p_int_sexo <- pval_guapa(lrtest(base_sexo, sexo)[2, 5])
  
  
  # INTERACTION WITH SEX - SPLINES #
  
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  datm<-subset2(dat2,"dat2$sexo==0")
  datm2<-datm[datm$mvltpalong<vars14[i],]
  
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  datf<-subset2(dat2,"dat2$sexo==1")
  datf2<-datf[datf$mvltpalong<vars14[i],]
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm,
    ties = "efron")
  coef_m<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm2,
    ties = "efron")
  coef_m2<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm,
    ties = "efron")
  
  p_lin<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linm<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlinm<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_m<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_m)<-c("x","yest","lci","uci")
  plot.data_m$coef<-ic_guapa2(guapa(plot.data_m$y),guapa(plot.data_m$lci),guapa(plot.data_m$uci))
  plot.data_mx<-plot.data_m[,c("x","coef")]
  plot.data_m$coef<-NULL
  colnames(plot.data_mx)<-c("mvltpa","HR")
  write.table(plot.data_mx,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_males_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_m<-subset2(plot.data_m,"plot.data_m$uci<=3")
  #plot.data_m$class<-"1"
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf,
    ties = "efron")
  coef_f<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf2,
    ties = "efron")
  coef_f2<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + aaa + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf,
    ties = "efron")
  
  p_lin<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linf<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlinf<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_f<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_f)<-c("x","yest","lci","uci")
  plot.data_f$coef<-ic_guapa2(guapa(plot.data_f$y),guapa(plot.data_f$lci),guapa(plot.data_f$uci))
  plot.data_fx<-plot.data_f[,c("x","coef")]
  plot.data_f$coef<-NULL
  colnames(plot.data_fx)<-c("mvltpa","HR")
  write.table(plot.data_fx,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_females_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_f<-subset2(plot.data_f,"plot.data_f$uci<=3")
  #plot.data_m$class<-"1"
  
  plot.data<-rbind(plot.data_m,plot.data_f)
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splinesex_",vars01[i],".jpg",sep="")
  labely<-paste(vars09[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("Female individuals:",
             "\nAll MVLTPA values, HR for +25 METs-min/d: ",coef_f,
             "\nMVLTPA values <150 METs-min/d, HR for +25 METs-min/d: ",coef_f2,
             "\nMale individuals:",
             "\nAll MVLTPA values, HR for +25 METs-min/d: ",coef_m,
             "\nMVLTPA values <150 METs-min/d, HR for +25 METs-min/d: ",coef_m2)
  
  figure<-ggplot() + 
    geom_ribbon(aes(x=plot.data_m$x, y=plot.data_m$y, ymin=plot.data_m$lci, ymax=plot.data_m$uci), alpha=0.25, fill='#1065B1') +
    geom_line(aes_string(x=plot.data_m$x, y=plot.data_m$y), color='#1065B1') +
    geom_ribbon(aes(x=plot.data_f$x, y=plot.data_f$y, ymin=plot.data_f$lci, ymax=plot.data_f$uci), alpha=0.25, fill='#B31529') +
    geom_line(aes_string(x=plot.data_f$x, y=plot.data_f$y), color='#B31529') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of moderate-vigorous LTPA\n(METs-min/day)"),y=labely) +
    annotate("text", x=max(plot.data_m$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  tab_ok<-rbind(tab_ok,cbind(median_time,sample_orig,outliers,excl_basal,samplesize,
                             nval_long_cont,coef_long_cont,pval_long_cont,pval_long_cont_ex,p_lrtest,
                             nval_long_q1,nval_long_q2,coef_long_qi,pval_long_qi,
                             min_val,min_coef,labelok,
                             p_int_sexo))
  tab<-rbind(tab,cbind(median_time,sample_orig,outliers,excl_basal,samplesize,
                       nval_long_cont,hr_long_cont,ic95a_long_cont,ic95b_long_cont,pval_long_cont,
                       pval_long_cont_ex,p_lrtest,
                       nval_long_q1,nval_long_q2,hr_long_qi,ic95a_long_qi,ic95b_long_qi,pval_long_qi,
                       min_val,min_coef,labelok))
  rownames(tab)<-vars01[i]
  rownames(tab_ok)<-vars01[i]
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splinedata_",vars01[i],".csv",sep="")
  write.table(tab_ok,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splineforestplot_",vars01[i],".csv",sep="")
  write.table(tab,file=namefile,sep=";",col.names=NA)
}


# OBESITY/ADIPOSITY AND OTHERS #

vars00<-c("bmi","wc","whtr","egfr","nlr","plat","plat")
varsxx<-c("obesity","adobesity","c_adip","ckd","nlr_hi","plat_lo","plat_hi")
vars01<-NULL
vars02<-NULL
vars03<-NULL
vars04<-NULL
vars05<-NULL
vars06<-NULL
vars07<-NULL
vars08<-c("Marginal cumulative incidence\nof obesity",
          "Marginal cumulative incidence\nof abdominal obesity",
          "Marginal cumulative incidence\nof central adiposity",
          "Marginal cumulative incidence\nof chronic kidney disease",
          "Marginal cumulative incidence\nof neutrophil-to-lymphocyte ratio ≥2.15",
          "Marginal cumulative incidence\nof low platelet levels",
          "Marginal cumulative incidence\nof high platelet levels")
vars09<-c("Onset of obesity",
          "Onset of abdominal obesity",
          "Onset of central adiposity",
          "Onset of chronic kidney disease",
          "Onset of neutrophil-to-lymphocyte ratio ≥2.15",
          "Onset of low platelet levels",
          "Onset of high platelet levels")
vars10<-c("bmi_ok","wc_ok","wc_ok","egfr_ok","nlr_ok","plat_ok","plat_ok")
vars14<-c(150,150,150,150,150,150,150) # Most beneficial MVLTPA range (a posteriori)
vars15<-c(80,80,80,80,80,80,80) # Maximum age to start the follow-up


for(i in 1:length(varsxx))
{
  vars01<-c(vars01,paste(varsxx[i],"_d",sep=""))
  vars03<-c(vars03,paste(varsxx[i],"_inicio",sep=""))
  vars05<-c(vars05,paste(varsxx[i],"_seg",sep=""))
}

for(i in 1:length(vars01))
{
  vars02<-c(vars02,paste("to",vars01[i],sep=""))
  vars04<-c(vars04,paste(vars01[i],"_when",sep=""))
  vars06<-c(vars06,paste("to",vars01[i],"_left",sep=""))
  vars07<-c(vars07,paste("to",vars01[i],"_right",sep=""))
}

for(i in 1:length(vars01))
{
  dat[,vars02[i]]<-with(dat,ifelse(dat[,vars01[i]]==1,(dat[,vars06[i]]+dat[,vars07[i]])/2,dat[,vars02[i]]))
}

for(i in 1:length(vars01))
  
{ 
  tab<-NULL
  tab_ok<-NULL
  
  labelok<-vars08[i]
  datx<-dat[dat[,vars10[i]]==1,]
  sample_orig<-dim(datx)[1]
  outliers<-length(which(datx$mvltpalong>600))
  datx<-datx[datx$mvltpalong<=600,]
  excl_basal<-length(which(datx[,vars03[i]]==1))
  datx<-datx[datx[,vars03[i]]==0,]
  samplesize<-dim(datx)[1]
  datx$xxx<-datx[, vars01[i]]
  datx$start_age<-datx$age00
  datx$stop_age<-datx$age00+(datx[,vars02[i]]/365.25)
  
  median_time<-ic_guapa(guapa(summary((datx[,vars02[i]]/365.25))[3]),guapa(summary((datx[,vars02[i]]/365.25))[2]),guapa(summary((datx[,vars02[i]]/365.25))[5]))
  
  # KAPLAN-MEIER CURVES #
  
  # ALL PARTICIPANTS #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  
  coef<-paste("≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00)
  wt <- weightit(formula=ps_formula, data=dat2, method="ps", estimand="ATE", stabilize=TRUE)
  dat2$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=dat2, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = vars08[i],
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_all_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  # ONLY WOMEN #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  daty<-dat2[dat2$sexo==1,]
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = daty,
    ties = "efron")
  
  coef<-paste("Only female individuals,\n≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00)
  wt <- weightit(formula=ps_formula, data=daty, method="ps", estimand="ATE", stabilize=TRUE)
  daty$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=daty, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = paste(vars08[i]," (women)",sep=""),
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_women_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  # ONLY MEN #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  daty<-dat2[dat2$sexo==0,]
  mod01 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      C(as.factor(mvltpa_cat2), base = 1) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = daty,
    ties = "efron")
  
  coef<-paste("Only male individuals,\n≥100 vs. <100 METs-min/d: HR = ",
              ic_guapa2(guapa(intervals(mod01)[1,1]),guapa(intervals(mod01)[1,2]),guapa(intervals(mod01)[1,3])),
              sep="")
  
  ps_formula <- mvltpa_cat2 ~
    as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 + 
    dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00)
  wt <- weightit(formula=ps_formula, data=daty, method="ps", estimand="ATE", stabilize=TRUE)
  daty$ipw <- wt$weights
  km_wt <- survfit(Surv(entry_age, exit_age, xxx)~mvltpa_cat2, data=daty, weights=ipw)
  
  km_obj <- ggsurvplot(
    km_wt,
    fun        = "event",
    conf.int   = TRUE,
    censor     = FALSE,
    risk.table = TRUE,
    risk.table.col = "strata",
    palette        = c("#2b2b2b", "#0072B2"),
    legend.title   = " ",
    legend.labs    = c("<100 METs-min/d",
                       "≥100 METs-min/d"),
    legend = "none",
    xlim       = c(60, vars15[i]),
    break.x.by = 5,
    xlab       = "Age (years)",
    ylab       = paste(vars08[i]," (men)",sep=""),
    risk.table.height = 0.18,
    ggtheme = theme_bw() +
      theme(
        axis.text.x  = element_text(size = 14),
        axis.text.y  = element_text(size = 14),
        axis.title   = element_text(size = 16, face = "bold"),
        legend.text  = element_text(size = 14),
        legend.title = element_text(size = 16))
  )
  
  km_obj$plot <- km_obj$plot +
    annotate("text",
             x      = 60 - 0.1,
             y      = 1.06,
             label  = coef,
             hjust  = 0, vjust = 1,
             size   = 4)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/km_men_",vars01[i],".jpg",sep="")
  ggsave(
    filename = namefile,
    plot     = km_obj$plot,
    units    = "px",
    width    = 8400,
    height   = 8400,
    dpi      = 1200,
    bg       = "white"
  )
  
  
  # SURVIVAL ANALYSES #
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  
  hr_long_cont<-intervals(mod02)[1,1]
  ic95a_long_cont<-intervals(mod02)[1,2]
  ic95b_long_cont<-intervals(mod02)[1,3]
  pval_long_cont<-intervals(mod02)[1,4]
  pval_long_cont_ex<-intervals(mod02)[1,4]
  hr_long_cont_ok<-guapa(hr_long_cont)
  ic95a_long_cont_ok<-guapa(ic95a_long_cont)
  ic95b_long_cont_ok<-guapa(ic95b_long_cont)
  coef_long_cont<-ic_guapa2(hr_long_cont_ok,ic95a_long_cont_ok,ic95b_long_cont_ok)
  coef_long_cont2<-coef_long_cont
  pval_long_cont<-pval_guapa(pval_long_cont)
  
  mod04 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpa_cat2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  hr_long_qi<-intervals(mod04)[1,1]
  ic95a_long_qi<-intervals(mod04)[1,2]
  ic95b_long_qi<-intervals(mod04)[1,3]
  pval_long_qi<-intervals(mod04)[1,4]
  hr_long_qi_ok<-guapa(hr_long_qi)
  ic95a_long_qi_ok<-guapa(ic95a_long_qi)
  ic95b_long_qi_ok<-guapa(ic95b_long_qi)
  coef_long_qi<-ic_guapa2(hr_long_qi_ok,ic95a_long_qi_ok,ic95b_long_qi_ok)
  pval_long_qi<-pval_guapa(pval_long_qi)
  
  nval_long_ca<-length(which(dat2[,vars01[i]]==1&!is.na(dat2$mvltpalong)))
  nval_long_co<-length(which(dat2[,vars01[i]]==0&!is.na(dat2$mvltpalong)))
  nval_long_cont<-paste("'",nval_long_ca,"/",nval_long_ca+nval_long_co,sep="")
  nval_long_q<-table(dat2[,vars01[i]],by=dat2$mvltpa_cat2)
  nval_long_q1<-paste("'",nval_long_q[2,1],"/",nval_long_q[2,1]+nval_long_q[1,1],sep="")
  nval_long_q2<-paste("'",nval_long_q[2,2],"/",nval_long_q[2,2]+nval_long_q[1,2],sep="")
  
  dat3<-subset2(dat2,"dat2$mvltpalong<vars14[i]")
  modxx <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat3,
    ties = "efron")
  hr_long_opt<-intervals(modxx)[1,1]
  ic95a_long_opt<-intervals(modxx)[1,2]
  ic95b_long_opt<-intervals(modxx)[1,3]
  pval_long_opt<-intervals(modxx)[1,4]
  pval_long_opt_ex<-intervals(modxx)[1,4]
  hr_long_opt_ok<-guapa(hr_long_opt)
  ic95a_long_opt_ok<-guapa(ic95a_long_opt)
  ic95b_long_opt_ok<-guapa(ic95b_long_opt)
  coef_long_opt<-ic_guapa2(hr_long_opt_ok,ic95a_long_opt_ok,ic95b_long_opt_ok)
  pval_long_opt<-pval_guapa(pval_long_opt)
  
  
  # SURVIVAL SPLINES #
  
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(sexo) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2,
    ties = "efron")
  
  p_lin<-pval_long_cont
  p_nonlin<-pval_guapa(summary(mfit)$coefficients[2,6])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  
  p_lin2<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlin2<-ifelse(p_nonlin=="<0.001"," < 0.001",
                    ifelse(p_nonlin=="<0.00001"," < 0.00001",paste(" = ",p_nonlin,sep="")))
  p_lrtest2<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data)<-c("x","yest","lci","uci")
  plot.data$coef<-ic_guapa2(guapa(plot.data$y),guapa(plot.data$lci),guapa(plot.data$uci))
  min_val<-guapa(plot.data$x[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))])
  min_coef<-plot.data$coef[which(plot.data$yest==min(plot.data$yest,na.rm=TRUE))]
  plot.datax<-plot.data[,c("x","coef")]
  plot.data$coef<-NULL
  colnames(plot.datax)<-c("mvltpa","HR")
  write.table(plot.datax,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/spline_",vars01[i],".jpg",sep="")
  labely<-paste(vars09[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("p-value for linearity",p_lin2,
             "\nHR for +25 METs-min/d:\n",coef_long_cont2,
             "\np-value for non-linearity",p_lrtest2,
             "\nHR for +25 METs-min/d (range: <",vars14[i]," METs-min/d):\n",coef_long_opt,sep="")
  
  figure<-ggplot(data=plot.data, aes_string(x=plot.data$x, y=plot.data$y)) + 
    geom_ribbon(aes_string(ymin=plot.data$lci, ymax=plot.data$uci), alpha=0.25, fill='#0072B2') +
    geom_line(aes_string(x=plot.data$x, y=plot.data$y), color='#0072B2') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of moderate-vigorous LTPA\n(METs-min/day)"),y=labely) +
    annotate("text", x=max(plot.data$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4.5) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  # INTERACTION TESTS #
  
  base_sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(mvltpalong, df = 4) + as.factor(sexo) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2, ties = "efron")
  sexo <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      ns(mvltpalong, df = 4) * as.factor(sexo) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = dat2, ties = "efron")
  p_int_sexo <- pval_guapa(lrtest(base_sexo, sexo)[2, 5])
  
  
  # INTERACTION WITH SEX - SPLINES #
  
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  datm<-subset2(dat2,"dat2$sexo==0")
  datm2<-datm[datm$mvltpalong<vars14[i],]
  
  dat2 <- datx |>
    dplyr::filter(age00 >= 60) |>
    dplyr::mutate(
      entry_age = pmax(start_age, 60),
      exit_age  = stop_age
    ) |>
    dplyr::filter(exit_age > entry_age)
  datf<-subset2(dat2,"dat2$sexo==1")
  datf2<-datf[datf$mvltpalong<vars14[i],]
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm,
    ties = "efron")
  coef_m<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm2,
    ties = "efron")
  coef_m2<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datm,
    ties = "efron")
  
  p_lin<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linm<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlinm<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_m<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_m)<-c("x","yest","lci","uci")
  plot.data_m$coef<-ic_guapa2(guapa(plot.data_m$y),guapa(plot.data_m$lci),guapa(plot.data_m$uci))
  plot.data_mx<-plot.data_m[,c("x","coef")]
  plot.data_m$coef<-NULL
  colnames(plot.data_mx)<-c("mvltpa","HR")
  write.table(plot.data_mx,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_males_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_m<-subset2(plot.data_m,"plot.data_m$uci<=3")
  #plot.data_m$class<-"1"
  
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf,
    ties = "efron")
  coef_f<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong2 +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf2,
    ties = "efron")
  coef_f2<-ic_guapa2(guapa(intervals(mod02)[1,1]),guapa(intervals(mod02)[1,2]),guapa(intervals(mod02)[1,3]))
  mod02 <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      mvltpalong +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf,
    ties = "efron")
  mfit <- coxph(
    Surv(entry_age, exit_age, xxx) ~
      pspline(mvltpalong, df=4) +
      as.factor(grup_int) + as.factor(escolar00) + as.factor(tobacco00) + bmi00 +
      dmed00 + kcal00 + cluster(idcluster2) + as.factor(diabetes00) + as.factor(hipercol00) + as.factor(hta00),
    data = datf,
    ties = "efron")
  
  p_lin<-pval_guapa(intervals(mod02)[1,4])
  p_lrtest<-pval_guapa(lrtest(mod02,mfit)[2,5])
  p_linf<-ifelse(p_lin=="<0.001"," < 0.001",
                 ifelse(p_lin=="<0.00001"," < 0.00001",paste(" = ",p_lin,sep="")))
  p_nonlinf<-ifelse(p_lrtest=="<0.001"," < 0.001",
                    ifelse(p_lrtest=="<0.00001"," < 0.00001",paste(" = ",p_lrtest,sep="")))
  
  ptemp<-termplot(mfit,term=1,se=TRUE,plot=FALSE)
  temp<-ptemp$mvltpalong
  temp<-temp[complete.cases(temp), ]
  center<-with(temp, y[x==min(temp$x,na.rm=TRUE)])
  ytemp<-temp$y+outer(temp$se,c(0,-z,z),'*')
  ci<-exp(ytemp-center)
  
  plot.data_f<-as.data.frame(cbind(temp$x,ci))
  colnames(plot.data_f)<-c("x","yest","lci","uci")
  plot.data_f$coef<-ic_guapa2(guapa(plot.data_f$y),guapa(plot.data_f$lci),guapa(plot.data_f$uci))
  plot.data_fx<-plot.data_f[,c("x","coef")]
  plot.data_f$coef<-NULL
  colnames(plot.data_fx)<-c("mvltpa","HR")
  write.table(plot.data_fx,file=paste("./Outputs2/",vars00[i],"/Survival/splinedetailed_females_",vars01[i],".csv",sep=""),
              sep=";",col.names=TRUE,row.names=FALSE)
  
  plot.data_f<-subset2(plot.data_f,"plot.data_f$uci<=3")
  #plot.data_m$class<-"1"
  
  plot.data<-rbind(plot.data_m,plot.data_f)
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splinesex_",vars01[i],".jpg",sep="")
  labely<-paste(vars09[i],"\n(multivariate adjusted hazard ratio)",sep="")
  leg<-paste("Female individuals:",
             "\nAll MVLTPA values, HR for +25 METs-min/d: ",coef_f,
             "\nMVLTPA values <150 METs-min/d, HR for +25 METs-min/d: ",coef_f2,
             "\nMale individuals:",
             "\nAll MVLTPA values, HR for +25 METs-min/d: ",coef_m,
             "\nMVLTPA values <150 METs-min/d, HR for +25 METs-min/d: ",coef_m2)
  
  figure<-ggplot() + 
    geom_ribbon(aes(x=plot.data_m$x, y=plot.data_m$y, ymin=plot.data_m$lci, ymax=plot.data_m$uci), alpha=0.25, fill='#1065B1') +
    geom_line(aes_string(x=plot.data_m$x, y=plot.data_m$y), color='#1065B1') +
    geom_ribbon(aes(x=plot.data_f$x, y=plot.data_f$y, ymin=plot.data_f$lci, ymax=plot.data_f$uci), alpha=0.25, fill='#B31529') +
    geom_line(aes_string(x=plot.data_f$x, y=plot.data_f$y), color='#B31529') +
    geom_hline(yintercept=1, linetype=2) +
    theme_bw() +
    scale_x_continuous(expand=c(0,0)) +
    labs(x=c("Cumulative mean of moderate-vigorous LTPA\n(METs-min/day)"),y=labely) +
    annotate("text", x=max(plot.data_m$x,na.rm=TRUE)*0.98, y=max(plot.data$uci,na.rm=TRUE), label=leg, vjust=1, hjust=1, size=4) +
    theme(axis.title.x = element_text(vjust=0.5, size=16, face="bold"), 
          axis.title.y = element_text(vjust=0.5, size=16, face="bold"),
          axis.text.x = element_text(size=16, colour = 'black'),
          axis.text.y = element_text(size=16, colour = 'black'),
          axis.ticks.x = element_line(colour = 'black'),
          axis.ticks.y = element_line(colour = 'black'),
          panel.grid.major = element_blank(),
          panel.grid.minor = element_blank(),
          axis.text.y.right = element_blank(),
          axis.ticks.y.right = element_blank())  
  
  ggsave(filename=namefile,units="px", width=8400, height=8400, dpi=1200, bg="white")
  par(las=1,cex=1.2,mar=c(6,6,2,0),bty="n",lheight=0.9)
  figure
  dev.off()
  
  tab_ok<-rbind(tab_ok,cbind(median_time,sample_orig,outliers,excl_basal,samplesize,
                             nval_long_cont,coef_long_cont,pval_long_cont,pval_long_cont_ex,p_lrtest,
                             nval_long_q1,nval_long_q2,coef_long_qi,pval_long_qi,
                             min_val,min_coef,labelok,
                             p_int_sexo))
  tab<-rbind(tab,cbind(median_time,sample_orig,outliers,excl_basal,samplesize,
                       nval_long_cont,hr_long_cont,ic95a_long_cont,ic95b_long_cont,pval_long_cont,
                       pval_long_cont_ex,p_lrtest,
                       nval_long_q1,nval_long_q2,hr_long_qi,ic95a_long_qi,ic95b_long_qi,pval_long_qi,
                       min_val,min_coef,labelok))
  rownames(tab)<-vars01[i]
  rownames(tab_ok)<-vars01[i]
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splinedata_",vars01[i],".csv",sep="")
  write.table(tab_ok,file=namefile,sep=";",col.names=NA)
  namefile<-paste("./Outputs2/",vars00[i],"/Survival/splineforestplot_",vars01[i],".csv",sep="")
  write.table(tab,file=namefile,sep=";",col.names=NA)
}

