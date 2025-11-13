library(lubridate)
library(survival)
library(gmodels)
library(survminer)
library(dplyr)
library(ggplot2)
library(epitools)
library(openxlsx)
library(writexl)
library(jskm)
library(cmprsk)
library(rms)
library(ggridges)
library(tidyr)
library(tidyverse)
library(broom)
library(survival)
library(knitr)
library(kableExtra)
library(Hmisc)
library(haven)
library(tableone)
library(charlsMAX)
library(dplyr)
library(survival)
library(mice)
library(broom)
# pretty count
n_fmt <- function(x) formatC(length(x), big.mark = ",", format = "d")
# read CSV 
read_csv_dt <- function(path) {
  stopifnot(file.exists(path))
  dt <- fread(path, showProgress = FALSE)
  setDT(dt)
  return(dt)
}
# UKB field-name resolver
ukb_cols_for_field <- function(dt, field_id) {
  patt <- paste0("^f\\.", field_id, "\\.")
  grep(patt, names(dt), value = TRUE)
}

# pick first non-NA across columns (for vectors)
coalesce_vec <- function(...) {
  Reduce(function(x, y) ifelse(is.na(x), y, x), list(...))
}

# earliest valid date across multiple date columns
earliest_date <- function(df, cols) {
  if (length(cols) == 0) return(rep(as.Date(NA), nrow(df)))
  tmp <- df[, cols, drop = FALSE]
  # Convert to Date if character
  tmp[] <- lapply(tmp, function(x) {
    if (inherits(x, "Date")) return(x)
    suppressWarnings(as.Date(x))
  })
  apply(tmp, 1, function(row) {
    vals <- row[!is.na(row)]
    if (length(vals) == 0) return(as.Date(NA))
    min(vals)
  }) |> as.Date(origin = "1970-01-01")
}

# any of numeric codes present in any of a set of columns
has_any_code <- function(df, cols, codes) {
  if (length(cols) == 0) return(rep(FALSE, nrow(df)))
  apply(df[, cols, drop = FALSE], 1, function(row) {
    any(na.omit(as.numeric(row)) %in% codes)
  })
}

# standardize ethnicity into broad groups using field 21000 codes
map_ethnicity <- function(code_vec) {
  out <- rep(NA_character_, length(code_vec))
  out[code_vec %in% c(1,2,3)]  <- "White"
  out[code_vec %in% c(4,5,6)]  <- "Mixed"
  out[code_vec %in% c(7,8,9)]  <- "Asian"
  out[code_vec %in% c(10,11,12)] <- "Black"
  out[code_vec %in% c(13,14,15)] <- "Other"
  out[is.na(code_vec)] <- "Unknown"
  out
}

# robust between function for year-month bounds inclusive
in_year_month_window <- function(y, m, start_ym = c(1951,10), end_ym = c(1956,3)) {
  start <- 12 * start_ym[1] + start_ym[2]
  end   <- 12 * end_ym[1]   + end_ym[2]
  ym    <- 12 * as.integer(y) + as.integer(m)
  !is.na(ym) & ym >= start & ym <= end
}

# frequency matching by age-sex-ethnicity bins
freq_match <- function(cases_df, controls_df, ratio = 1, age_breaks = NULL) {
  if (is.null(age_breaks)) {
    # 5-year bins by default
    mn <- floor(min(c(cases_df$age, controls_df$age), na.rm = TRUE))
    mx <- ceiling(max(c(cases_df$age, controls_df$age), na.rm = TRUE))
    age_breaks <- seq(mn, mx + 5, by = 5)
  }
  bin_cut <- function(x) cut(x, breaks = age_breaks, right = FALSE, include.lowest = TRUE)
  cases_df <- cases_df %>%
    mutate(age_bin = bin_cut(age)) %>%
    mutate(strata = paste(age_bin, sex, ethnicity, sep = "|"))
  controls_df <- controls_df %>%
    mutate(age_bin = bin_cut(age)) %>%
    mutate(strata = paste(age_bin, sex, ethnicity, sep = "|"))
  take_list <- vector("list", length = 0)
  for (s in unique(cases_df$strata)) {
    need <- sum(cases_df$strata == s) * ratio
    pool <- controls_df %>% filter(strata == s)
    if (nrow(pool) == 0) next
    k <- min(need, nrow(pool))
    take <- pool %>% slice_sample(n = k)
    take_list[[length(take_list) + 1]] <- take
  }
  matched_controls <- bind_rows(take_list)
  matched_controls
}

main_path      <- "ukb_main.csv"            
withdrawn_path <- "withdrawn_eids.csv"      # single column 'eid' (numeric) of withdrawn participants
stopifnot(file.exists(main_path))

ukb <- read_csv_dt(main_path)

withdrawn_eids <- if (file.exists(withdrawn_path)) {
  fread(withdrawn_path)[[1]]
} else {
  numeric(0)
}

# EID
stopifnot("f.eid" %in% names(ukb))
setnames(ukb, "f.eid", "eid")

# Sex (31)
sex_cols <- ukb_cols_for_field(ukb, 31)
stopifnot(length(sex_cols) >= 1)
ukb$sex <- factor(ifelse(ukb[[sex_cols[1]]] == 0 | ukb[[sex_cols[1]]] == "0", NA,
                         ifelse(ukb[[sex_cols[1]]] == 1 | ukb[[sex_cols[1]]] == "1", "Male", "Female")),
                  levels = c("Male","Female"))

# Ethnicity (21000)
eth_cols <- ukb_cols_for_field(ukb, 21000)
eth_code <- suppressWarnings(as.integer(ukb[[eth_cols[1]]]))
ukb$ethnicity <- factor(map_ethnicity(eth_code),
                        levels = c("White","Mixed","Asian","Black","Other","Unknown"))

# Year / Month of birth (34 / 52)
y_cols <- ukb_cols_for_field(ukb, 34)
m_cols <- ukb_cols_for_field(ukb, 52)
ukb$yob <- suppressWarnings(as.integer(ukb[[y_cols[1]]]))
ukb$mob <- suppressWarnings(as.integer(ukb[[m_cols[1]]]))

# Baseline/Assessment date (53)
d53_cols <- ukb_cols_for_field(ukb, 53)
ukb$baseline_date <- suppressWarnings(as.Date(ukb[[d53_cols[1]]]))

# Age at baseline (prefer 21003 integer; otherwise compute from DOB (approx))
age_cols <- ukb_cols_for_field(ukb, 21003)
if (length(age_cols) > 0) {
  ukb$age <- suppressWarnings(as.integer(ukb[[age_cols[1]]]))
} else {
  # Fallback: year-month birth to mid-month vs baseline date
  dob_mid <- as.Date(paste0(ukb$yob, "-", ifelse(is.na(ukb$mob), 6, ukb$mob), "-15"))
  ukb$age <- floor(time_length(interval(dob_mid, ukb$baseline_date), unit = "years"))
}

# Country of birth (1647 + 20115)
c1647 <- ukb_cols_for_field(ukb, 1647)
c20115 <- ukb_cols_for_field(ukb, 20115)
ukb$born_non_uk_flag <- FALSE
if (length(c20115) > 0) {
  ukb$born_non_uk_flag <- ukb$born_non_uk_flag | !is.na(ukb[[c20115[1]]])
}
if (length(c1647) > 0) {
  val <- suppressWarnings(as.integer(ukb[[c1647[1]]]))
  ukb$born_non_uk_flag <- ukb$born_non_uk_flag | (!is.na(val) & !(val %in% c(1,2,3,4)))
}

# Part of a multiple birth (1777)
mb_cols <- ukb_cols_for_field(ukb, 1777)
ukb$multiple_birth_flag <- if (length(mb_cols) > 0) {
  x <- suppressWarnings(as.integer(ukb[[mb_cols[1]]]))
  !is.na(x) & x == 1
} else FALSE

# Adopted as a child (1767)
ad_cols <- ukb_cols_for_field(ukb, 1767)
ukb$adopted_flag <- if (length(ad_cols) > 0) {
  x <- suppressWarnings(as.integer(ukb[[ad_cols[1]]]))
  !is.na(x) & x == 1
} else FALSE

###############CVD
ukb$incident_cvd=NA

cvd=function(x){
  for (i in 1:nrow(ukb)) {
    if (is.na(ukb$incident_cvd[i])&grepl("I20|I21|I22|I23|I24|I25|I60|I61|I62|I63|I64",ukb[[x]][i])) {
      ukb$incident_cvd[i]=2
      print(i)
    }
  }
  return(ukb$incident_cvd)
}

for (p in ls(ukb,pattern="41270")) {
  ukb$incident_cvd=cvd(p)
}   

ukb$incident_cvd[is.na(ukb$incident_cvd)]=1
table(ukb$incident_cvd)


#cvd time
ukb$incident_cvd_time = NA
yuyu=function(y){
  y=gsub("41270_","41280_a",y)
  return(y)
}
cvd=function(x){
  for (i in which(ukb$incident_cvd==2)) {
    if (is.na(ukb$incident_cvd_time[i])&grepl("I20|I21|I22|I23|I24|I25|I60|I61|I62|I63|I64",ukb[[x]][i])){
      ukb$incident_cvd_time[i]=ukb[[yuyu(x)]][i]
    }
  }
  return(ukb$incident_cvd_time)
}

for (n in ls(ukb,pattern="41270_")) {
  ukb$incident_cvd_time=cvd(n)
}   

table(is.na(ukb$incident_cvd_time)==FALSE)
ukb$incident_cvd_time=ymd(ukb$incident_cvd_time)-ymd(ukb$p53_i0)
ukb$incident_cvd_time=as.numeric(ukb$incident_cvd_time)
summary(ukb$incident_cvd_time)
table(ukb$incident_cvd_time<0)

ukb$survival_time=ymd(ukb$p40000_i0)-ymd(ukb$p53_i0)
ukb$survival_time=as.numeric(ukb$survival_time)
summary(ukb$survival_time)
ukb$incident_cvd_time <- ifelse(is.na(ukb$incident_cvd_time), 
                                 ifelse(is.na(ukb$survival_time), 
                                        as.numeric(ymd('2023-03-25') - ymd(ukb$p53_i0)), 
                                        ukb$survival_time), 
                                 ukb$incident_cvd_time)
summary(ukb$incident_cvd_time)

###############AF
ukb$incident_AF=NA

AF=function(x){
  for (i in 1:nrow(ukb)) {
    if (is.na(ukb$incident_AF[i])&grepl("I48",ukb[[x]][i])) {
      ukb$incident_AF[i]=2
      print(i)
    }
  }
  return(ukb$incident_AF)
}

for (p in ls(ukb,pattern="41270")) {
  ukb$incident_AF=AF(p)
}   

ukb$incident_AF[is.na(ukb$incident_AF)]=1
table(ukb$incident_AF)


#AF time
ukb$incident_AF_time = NA
yuyu=function(y){
  y=gsub("41270_","41280_a",y)
  return(y)
}
AF=function(x){
  for (i in which(ukb$incident_AF==2)) {
    if (is.na(ukb$incident_AF_time[i])&grepl("I48",ukb[[x]][i])){
      ukb$incident_AF_time[i]=ukb[[yuyu(x)]][i]
    }
  }
  return(ukb$incident_AF_time)
}

for (n in ls(ukb,pattern="41270_")) {
  ukb$incident_AF_time=AF(n)
}   

table(is.na(ukb$incident_AF_time)==FALSE)
ukb$incident_AF_time=ymd(ukb$incident_AF_time)-ymd(ukb$p53_i0)
ukb$incident_AF_time=as.numeric(ukb$incident_AF_time)
summary(ukb$incident_AF_time)
table(ukb$incident_AF_time<0)

ukb$survival_time=ymd(ukb$p40000_i0)-ymd(ukb$p53_i0)
ukb$survival_time=as.numeric(ukb$survival_time)
summary(ukb$survival_time)
ukb$incident_AF_time <- ifelse(is.na(ukb$incident_AF_time), 
                                ifelse(is.na(ukb$survival_time), 
                                       as.numeric(ymd('2023-03-25') - ymd(ukb$p53_i0)), 
                                       ukb$survival_time), 
                                ukb$incident_AF_time)
summary(ukb$incident_AF_time)

###############HF
ukb$incident_HF=NA

HF=function(x){
  for (i in 1:nrow(ukb)) {
    if (is.na(ukb$incident_HF[i])&grepl("I50",ukb[[x]][i])) {
      ukb$incident_HF[i]=2
      print(i)
    }
  }
  return(ukb$incident_HF)
}

for (p in ls(ukb,pattern="41270")) {
  ukb$incident_HF=HF(p)
}   

ukb$incident_HF[is.na(ukb$incident_HF)]=1
table(ukb$incident_HF)


#HF time
ukb$incident_HF_time = NA
yuyu=function(y){
  y=gsub("41270_","41280_a",y)
  return(y)
}
HF=function(x){
  for (i in which(ukb$incident_HF==2)) {
    if (is.na(ukb$incident_HF_time[i])&grepl("I50",ukb[[x]][i])){
      ukb$incident_HF_time[i]=ukb[[yuyu(x)]][i]
    }
  }
  return(ukb$incident_HF_time)
}

for (n in ls(ukb,pattern="41270_")) {
  ukb$incident_HF_time=HF(n)
}   

table(is.na(ukb$incident_HF_time)==FALSE)
ukb$incident_HF_time=ymd(ukb$incident_HF_time)-ymd(ukb$p53_i0)
ukb$incident_HF_time=as.numeric(ukb$incident_HF_time)
summary(ukb$incident_HF_time)
table(ukb$incident_HF_time<0)

ukb$survival_time=ymd(ukb$p40000_i0)-ymd(ukb$p53_i0)
ukb$survival_time=as.numeric(ukb$survival_time)
summary(ukb$survival_time)
ukb$incident_HF_time <- ifelse(is.na(ukb$incident_HF_time), 
                               ifelse(is.na(ukb$survival_time), 
                                      as.numeric(ymd('2023-03-25') - ymd(ukb$p53_i0)), 
                                      ukb$survival_time), 
                               ukb$incident_HF_time)
summary(ukb$incident_HF_time)

ukb <- subset(ukb, incident_CVD_time >= 0 & 
                      incident_AF_time >= 0 & 
                      incident_HF_time >= 0)
# -----------------------------
# AF (I48) 131350; HF (I50) 131354
fo_af_cols <- ukb_cols_for_field(ukb, 131350)
fo_hf_cols <- ukb_cols_for_field(ukb, 131354)

# IHD I20-I25: 131296, 131298, 131300, 131302, 131304, 131306
fo_ihd_ids <- c(131296, 131298, 131300, 131302, 131304, 131306)
fo_ihd_cols <- unlist(lapply(fo_ihd_ids, \(id) ukb_cols_for_field(ukb, id)))

# Cerebrovascular I60–I69: 131360, 131362, 131364, 131366, 131368, 131370, 131372, 131374, 131376, 131378
fo_cbv_ids <- c(131360,131362,131364,131366,131368,131370,131372,131374,131376,131378)
fo_cbv_cols <- unlist(lapply(fo_cbv_ids, \(id) ukb_cols_for_field(ukb, id)))

# Compute earliest dates
ukb$af_first_date  <- earliest_date(ukb, fo_af_cols)
ukb$hf_first_date  <- earliest_date(ukb, fo_hf_cols)
ukb$ihd_first_date <- earliest_date(ukb, fo_ihd_cols)
ukb$cbv_first_date <- earliest_date(ukb, fo_cbv_cols)

# -----------------------------
# 4) Self-reported codes (20002) as supplement
# -----------------------------
sr_cols <- ukb_cols_for_field(ukb, 20002)

# Codes: AF=1471, HF=1076, Angina=1074, MI=1075, Stroke=1081 (Data-Coding 6)
codes_af     <- c(1471, 1483)           # include atrial flutter
codes_hf     <- c(1076)
codes_cvd_sr <- c(1074, 1075, 1081)     # angina, MI, stroke; add as needed

ukb$sr_has_af  <- has_any_code(ukb, sr_cols, codes_af)
ukb$sr_has_hf  <- has_any_code(ukb, sr_cols, codes_hf)
ukb$sr_has_cvd <- has_any_code(ukb, sr_cols, codes_cvd_sr)

# -----------------------------
# 5) Define prevalent disease prior to baseline
# -----------------------------
# Rule: prevalent if first-occurrence date <= baseline; or (no date available) self-report indicates history
ukb$prev_af <- (!is.na(ukb$af_first_date) & ukb$af_first_date <= ukb$baseline_date) | ukb$sr_has_af
ukb$prev_hf <- (!is.na(ukb$hf_first_date) & ukb$hf_first_date <= ukb$baseline_date) | ukb$sr_has_hf

# CVD broader: IHD or cerebrovascular (first-occurrence) before baseline OR self-reported CVD codes
ukb$prev_cvd <- (
  (!is.na(ukb$ihd_first_date) & ukb$ihd_first_date <= ukb$baseline_date) |
    (!is.na(ukb$cbv_first_date) & ukb$cbv_first_date <= ukb$baseline_date)
) | ukb$sr_has_cvd

# -----------------------------
# 6) Build cohort & apply exclusions
# -----------------------------
# Start: participants born between 1951-10 and 1956-03
ukb$in_birth_window <- in_year_month_window(ukb$yob, ukb$mob, c(1951,10), c(1956,3))

start_ids <- ukb %>% filter(in_birth_window) %>% pull(eid)
cat("Start (born 1951-10 to 1956-03): ", n_fmt(start_ids), "\n")

# Exclude: prevalent CVD/HF/AF
exc_prev <- ukb %>%
  filter(in_birth_window) %>%
  mutate(any_prev = prev_cvd | prev_hf | prev_af) %>%
  filter(any_prev) %>% pull(eid)

# Exclude: born outside UK
exc_born_out <- ukb %>%
  filter(in_birth_window & born_non_uk_flag) %>% pull(eid)

# Exclude: multiple birth
exc_mb <- ukb %>%
  filter(in_birth_window & multiple_birth_flag) %>% pull(eid)

# Exclude: adopted
exc_adopt <- ukb %>%
  filter(in_birth_window & adopted_flag) %>% pull(eid)

# Exclude: withdrawn
exc_withdrawn <- intersect(start_ids, withdrawn_eids)

# Combine exclusions
exclude_all <- unique(c(exc_prev, exc_born_out, exc_mb, exc_adopt, exc_withdrawn))

post_excl <- setdiff(start_ids, exclude_all)

# Report numbers (similar to flowchart)
cat("Excluded total: ", n_fmt(exclude_all), "\n")
cat("  - Prevalent CVD/HF/AF: ", n_fmt(exc_prev), "\n")
cat("  - Born outside UK:     ", n_fmt(exc_born_out), "\n")
cat("  - Multiple births:     ", n_fmt(exc_mb), "\n")
cat("  - Adopted:             ", n_fmt(exc_adopt), "\n")
cat("  - Withdrawn:           ", n_fmt(exc_withdrawn), "\n")
cat("Remaining after exclusions: ", n_fmt(post_excl), "\n")

# -----------------------------
# 7) Frequency matching (age, sex, ethnicity)
# -----------------------------
# Assumption:
ukb$exposed_flag <- FALSE
ukb$exposed_flag[ukb$eid %in% sample(post_excl, size = floor(length(post_excl)/4))] <- TRUE

eligible <- ukb %>% filter(eid %in% post_excl)

cases    <- eligible %>% filter(exposed_flag) %>% select(eid, age, sex, ethnicity)
controls <- eligible %>% filter(!exposed_flag) %>% select(eid, age, sex, ethnicity)

matched_controls <- freq_match(cases, controls, ratio = 1) %>%
  mutate(matched = TRUE)

final_ids <- unique(c(cases$eid, matched_controls$eid))

cat("Cases (exposed) for matching: ", n_fmt(cases$eid), "\n")
cat("Matched controls:             ", n_fmt(matched_controls$eid), "\n")
cat("Participants included in analysis: ", n_fmt(final_ids), "\n")

analysis_df <- eligible %>%
  filter(eid %in% final_ids) %>%
  mutate(group = ifelse(exposed_flag, "case", "control")) %>%
  select(eid, group, age, sex, ethnicity, yob, mob, baseline_date)

excl_log <- tibble(
  eid = c(exc_prev, exc_born_out, exc_mb, exc_adopt, exc_withdrawn),
  reason = c(
    rep("prev_cvd_hf_af", length(exc_prev)),
    rep("born_outside_uk", length(exc_born_out)),
    rep("multiple_birth", length(exc_mb)),
    rep("adopted", length(exc_adopt)),
    rep("withdrawn", length(exc_withdrawn))
  )
) %>% distinct()
fwrite(analysis_df, "ukb_analysis_cohort.csv")
fwrite(excl_log,    "ukb_exclusion_log.csv")

stopifnot(all(eligible$in_birth_window))
# Verify matching strata overlap
summ_case <- cases    %>% mutate(k="cases")    %>% group_by(k, sex, ethnicity) %>% summarise(n=n(), .groups="drop")
summ_ctrl <- matched_controls %>% mutate(k="controls") %>% group_by(k, sex, ethnicity) %>% summarise(n=n(), .groups="drop")
print(bind_rows(summ_case, summ_ctrl) %>% arrange(sex, ethnicity, k))
rm(list = c("age_cols","ad_cols","c1647","c20115","cases","controls","d53_cols",
            "eth_cols","eth_code","fo_af_cols","fo_hf_cols","fo_cbv_cols","fo_ihd_cols",
            "m_cols","mb_cols","sr_cols","y_cols"))
gc()

# Evaluate and assign each condition sequentially
ukb$birth_group <- ifelse(
  (ukb$year_birth == 1951 & ukb$month_birth %in% c("October", "November", "December")) | 
    (ukb$year_birth == 1952 & ukb$month_birth %in% c("January", "February", "March")),
  1,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1952 & ukb$month_birth %in% c("April", "May", "June", "July", "August", "September")),
  2,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1952 & ukb$month_birth %in% c("October", "November", "December")),
  3,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1953 & ukb$month_birth %in% c("January", "February", "March")),
  3,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1953 & ukb$month_birth %in% c("April", "May", "June", "July", "August", "September")),
  4,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1953 & ukb$month_birth %in% c("October", "November", "December")),
  5,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1954 & ukb$month_birth %in% c("January", "February", "March", "April", "May", "June")),
  5,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1954 & ukb$month_birth %in% c("July", "August", "September", "October", "November", "December")),
  6,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1955 & ukb$month_birth %in% c("January", "February", "March", "April", "May", "June")),
  7,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1955 & ukb$month_birth %in% c("July", "August", "September", "October", "November", "December")),
  8,
  ukb$birth_group
)

ukb$birth_group <- ifelse(
  (ukb$year_birth == 1956 & ukb$month_birth %in% c("January", "February", "March")),
  9,
  ukb$birth_group
)

table(ukb$birth_group)
sum(!is.na(ukb$birth_group))

# The number of numbers less than 6
sum(ukb$birth_group < 6, na.rm = TRUE)

# The number of numbers more than 6
sum(ukb$birth_group >= 6, na.rm = TRUE)
ukb <- ukb %>% filter(!is.na(birth_group))
names(ukb) <- make.names(names(ukb), unique = TRUE)
# Filter out rows where the birth_group column contains NA.
ukb <- ukb %>% filter(!is.na(birth_group))
#
ukb$birth_group_1=NA
ukb$birth_group_1[ukb$birth_group==1|ukb$birth_group==2|ukb$birth_group==3|ukb$birth_group==4]=1
ukb$birth_group_1[ukb$birth_group==6]=2
ukb$birth_group_1[ukb$birth_group==7|ukb$birth_group==8|ukb$birth_group==9]=3
table(ukb$birth_group_1)
#
ukb$birth_group_all=NA
ukb$birth_group_all[ukb$birth_group==6|ukb$birth_group==7|ukb$birth_group==8|ukb$birth_group==9]=1
ukb$birth_group_all[ukb$birth_group==1|ukb$birth_group==2|ukb$birth_group==3|ukb$birth_group==4|ukb$birth_group==5]=2
table(ukb$birth_group_all)

### Table 1
# Birth weight (20022)
bw_cols <- ukb_cols_for_field(ukb, 20022)
if (length(bw_cols) > 0) {
  ukb[, birth_weight := suppressWarnings(as.numeric(get(bw_cols[1])))]
} else {
  ukb[, birth_weight := NA_real_]
}

# Mother smoked around birth (1787)
ms_cols <- ukb_cols_for_field(ukb, 1787)
if (length(ms_cols) > 0) {
  v <- ukb[[ms_cols[1]]]
  if (is.numeric(v)) {
    ukb[, maternal_smoke := fifelse(v == 1, 1L, fifelse(v == 0, 0L, NA_integer_))]
  } else {
    ukb[, maternal_smoke := fifelse(str_detect(tolower(as.character(v)), "yes"), 1L,
                                    fifelse(str_detect(tolower(as.character(v)), "no"), 0L, NA_integer_))]
  }
} else {
  ukb[, maternal_smoke := NA_integer_]
}

# Breastfed as baby (1677)
bf_cols <- ukb_cols_for_field(ukb, 1677)
if (length(bf_cols) > 0) {
  v <- ukb[[bf_cols[1]]]
  if (is.numeric(v)) {
    ukb[, breastfed := fifelse(v == 1, 1L, fifelse(v == 0, 0L, NA_integer_))]
  } else {
    ukb[, breastfed := fifelse(str_detect(tolower(as.character(v)), "yes"), 1L,
                               fifelse(str_detect(tolower(as.character(v)), "no"), 0L, NA_integer_))]
  }
} else {
  ukb[, breastfed := NA_integer_]
}

# Father still alive (1797)
fa_cols <- ukb_cols_for_field(ukb, 1797)
if (length(fa_cols) > 0) {
  v <- ukb[[fa_cols[1]]]
  if (is.numeric(v)) {
    ukb[, father_alive := fifelse(v == 1, 1L, fifelse(v == 0, 0L, NA_integer_))]
  } else {
    ukb[, father_alive := fifelse(str_detect(tolower(as.character(v)), "yes"), 1L,
                                  fifelse(str_detect(tolower(as.character(v)), "no"), 0L, NA_integer_))]
  }
} else {
  ukb[, father_alive := NA_integer_]
}

# 4) Parents' illnesses 
parent_any_has <- function(df, field_id, keywords = NULL, numeric_codes = NULL) {
  cols <- ukb_cols_for_field(df, field_id)
  if (length(cols) == 0) return(rep(NA_integer_, nrow(df)))
  vals <- df[, ..cols]
  if (!is.null(numeric_codes)) {
    has <- apply(vals, 1, function(x) any(!is.na(x) & as.numeric(x) %in% numeric_codes))
    return(as.integer(has))
  }
  if (!is.null(keywords)) {
    has <- apply(vals, 1, function(x) {
      any(str_detect(tolower(paste(x, collapse = " | ")), keywords))
    })
    return(as.integer(has))
  }
  rep(NA_integer_, nrow(df))
}
KW_HEART   <- "heart"
KW_STROKE  <- "stroke"
KW_DIAB    <- "diabet"
KW_HYPER   <- "high blood|hypertension"
HEART_CODES  <- NULL
STROKE_CODES <- NULL
DIAB_CODES   <- NULL
HYPER_CODES  <- NULL

# father/mother indicators
ukb[, father_heart  := parent_any_has(ukb, 20107, keywords = KW_HEART,  numeric_codes = HEART_CODES)]
ukb[, father_stroke := parent_any_has(ukb, 20107, keywords = KW_STROKE, numeric_codes = STROKE_CODES)]
ukb[, father_diab   := parent_any_has(ukb, 20107, keywords = KW_DIAB,   numeric_codes = DIAB_CODES)]
ukb[, father_htn    := parent_any_has(ukb, 20107, keywords = KW_HYPER,  numeric_codes = HYPER_CODES)]
ukb[, mother_heart  := parent_any_has(ukb, 20110, keywords = KW_HEART,  numeric_codes = HEART_CODES)]
ukb[, mother_stroke := parent_any_has(ukb, 20110, keywords = KW_STROKE, numeric_codes = STROKE_CODES)]
ukb[, mother_diab   := parent_any_has(ukb, 20110, keywords = KW_DIAB,   numeric_codes = DIAB_CODES)]
ukb[, mother_htn    := parent_any_has(ukb, 20110, keywords = KW_HYPER,  numeric_codes = HYPER_CODES)]
# Combine to parental conditions
ukb[, parent_cvd := as.integer(pmax(father_heart, father_stroke, mother_heart, mother_stroke, na.rm = TRUE))]
ukb[, parent_diab := as.integer(pmax(father_diab, mother_diab, na.rm = TRUE))]
ukb[, parent_htn  := as.integer(pmax(father_htn, mother_htn, na.rm = TRUE))]

#tests
fmt_pct <- function(x, digits = 1) sprintf(paste0("%.", digits, "f"), x)
fmt_pp  <- function(x, digits = 1) sprintf(paste0("%.", digits, "f"), x)
pval_str <- function(p) {
  if (is.na(p)) return("NA")
  if (p < 0.001) "<0.001" else sprintf("%.3f", p)
}
# Continuous variable summary
summ_cont <- function(df, var, group) {
  d <- df %>% filter(!is.na(.data[[var]]), !is.na(.data[[group]]))
  tot_n <- nrow(d)
  m_all <- mean(d[[var]], na.rm = TRUE); sd_all <- sd(d[[var]], na.rm = TRUE)
  d0 <- d %>% filter(.data[[group]] == 0)
  d1 <- d %>% filter(.data[[group]] == 1)
  m0 <- mean(d0[[var]], na.rm = TRUE); sd0 <- sd(d0[[var]], na.rm = TRUE); n0 <- nrow(d0)
  m1 <- mean(d1[[var]], na.rm = TRUE); sd1 <- sd(d1[[var]], na.rm = TRUE); n1 <- nrow(d1)
  # Welch t-test
  p <- tryCatch(t.test(d1[[var]], d0[[var]])$p.value, error = function(e) NA_real_)
  tibble(
    characteristic = var,
    total = sprintf("%.1f (%.1f)", m_all, sd_all),
    rationed = sprintf("%.1f (%.1f)", m1, sd1),
    not_rationed = sprintf("%.1f (%.1f)", m0, sd0),
    diff_pp = NA_character_,
    p_value = pval_str(p),
    n_total = tot_n, n_rationed = n1, n_not = n0,
    is_continuous = TRUE
  )
}
summ_binary <- function(df, var, label, group) {
  d <- df %>% filter(!is.na(.data[[var]]), !is.na(.data[[group]]))
  tot_n <- nrow(d)
  # totals
  p_all <- mean(d[[var]] == 1, na.rm = TRUE) * 100
  # by group
  d0 <- d %>% filter(.data[[group]] == 0)
  d1 <- d %>% filter(.data[[group]] == 1)
  p0 <- mean(d0[[var]] == 1, na.rm = TRUE) * 100; n0 <- nrow(d0)
  p1 <- mean(d1[[var]] == 1, na.rm = TRUE) * 100; n1 <- nrow(d1)
  # difference and test
  diff <- p1 - p0
  tab <- table(d[[group]], d[[var]])
  if (all(dim(tab) == c(2,2))) {
    p <- suppressWarnings(chisq.test(tab)$p.value)
  } else {
    p <- NA_real_
  }
  tibble(
    characteristic = label,
    total = sprintf("%d (%.1f)", round(tot_n * p_all/100), p_all),
    rationed = sprintf("%d (%.1f)", round(n1 * p1/100), p1),
    not_rationed = sprintf("%d (%.1f)", round(n0 * p0/100), p0),
    diff_pp = fmt_pp(diff),
    p_value = pval_str(p),
    n_total = tot_n, n_rationed = n1, n_not = n0,
    is_continuous = FALSE
  )
}
# Multi-category variable => one row per category
summ_categorical <- function(df, var, cat_levels, labels = NULL, group) {
  if (is.null(labels)) labels <- cat_levels
  out <- map2_dfr(cat_levels, labels, function(lv, lab) {
    vv <- df[[var]]
    d <- df %>% filter(!is.na(vv), !is.na(.data[[group]]))
    tot_n <- nrow(d)
    # overall
    p_all <- mean(d[[var]] == lv, na.rm = TRUE) * 100
    # by group
    d0 <- d %>% filter(.data[[group]] == 0)
    d1 <- d %>% filter(.data[[group]] == 1)
    p0 <- mean(d0[[var]] == lv, na.rm = TRUE) * 100; n0 <- nrow(d0)
    p1 <- mean(d1[[var]] == lv, na.rm = TRUE) * 100; n1 <- nrow(d1)
    diff <- p1 - p0
    # chi-square on the whole multi-cat (once) 
    tab <- table(d[[group]], d[[var]])
    p <- suppressWarnings(chisq.test(tab)$p.value)
    tibble(
      characteristic = lab,
      total = sprintf("%d (%.1f)", round(tot_n * p_all/100), p_all),
      rationed = sprintf("%d (%.1f)", round(n1 * p1/100), p1),
      not_rationed = sprintf("%d (%.1f)", round(n0 * p0/100), p0),
      diff_pp = fmt_pp(diff),
      p_value = pval_str(p),
      n_total = tot_n, n_rationed = n1, n_not = n0,
      is_continuous = FALSE
    )
  })
  out
}



#########grep outcome
stopifnot(file.exists(main_path))
ukb <- fread(main_path, showProgress = FALSE)
setDT(ukb)

# Return columns for a UKB field id
ukb_cols_for_field <- function(dt, field_id) {
  patt <- paste0("^f\\.", field_id, "\\.")
  grep(patt, names(dt), value = TRUE)
}

# Coalesce date across multiple columns (take earliest non-NA)
earliest_date <- function(df, cols) {
  if (length(cols) == 0) return(rep(as.Date(NA), nrow(df)))
  tmp <- df[, ..cols]
  # Normalize to Date
  for (j in seq_along(cols)) {
    x <- tmp[[j]]
    if (!inherits(x, "Date")) {
      sup <- suppressWarnings(as.Date(x))
      tmp[[j]] <- sup
    }
  }
  # row-wise min
  res <- apply(tmp, 1, function(row) {
    v <- row[!is.na(row)]
    if (length(v) == 0) return(NA_real_)
    as.numeric(min(v))
  })
  as.Date(res, origin = "1970-01-01")
}

# A safe row-wise min for two date vectors
pmin_date <- function(...) {
  args <- list(...)
  # convert to numeric for pmin with NAs
  num <- lapply(args, function(x) as.numeric(x))
  out <- do.call(pmin, c(num, list(na.rm = TRUE)))
  as.Date(out, origin = "1970-01-01")
}

# Extract earliest HES ICD-10 date using paired arrays:
get_earliest_from_hes_arrays <- function(df, codes_cols, date_cols, patterns) {
  if (length(codes_cols) == 0 || length(date_cols) == 0) {
    return(rep(as.Date(NA), nrow(df)))
  }
  # Ensure same length (UKB exports usually align arrays by index)
  K <- min(length(codes_cols), length(date_cols))
  codes_cols <- codes_cols[seq_len(K)]
  date_cols  <- date_cols[seq_len(K)]
  # pre-compile pattern
  patt <- paste(patterns, collapse = "|")
  # Iterate by rows (data.table fast subset)
  out <- vector("list", nrow(df))
  for (i in seq_len(nrow(df))) {
    codes <- as.character(unlist(df[i, ..codes_cols]))
    dts   <- as.character(unlist(df[i, ..date_cols]))
    # normalize
    dts   <- suppressWarnings(as.Date(dts))
    sel   <- !is.na(codes) & grepl(patt, codes)
    if (!any(sel)) {
      out[[i]] <- as.Date(NA)
    } else {
      out[[i]] <- suppressWarnings(min(dts[sel], na.rm = TRUE))
    }
  }
  as.Date(unlist(out), origin = "1970-01-01")
}

# Detect "First Occurrence" (FO) columns for a list of field IDs and take earliest date
get_earliest_from_first_occurrence <- function(df, field_ids) {
  cols <- unlist(lapply(field_ids, \(id) ukb_cols_for_field(df, id)))
  earliest_date(df, cols)
}

# Event/censor time builder
build_surv_vars <- function(start_date, event_date, death_date, study_end) {
  # Incident event: must be strictly after start
  ev_valid <- !is.na(event_date) & !is.na(start_date) & (event_date > start_date)
  # Censor date = earliest of death or study_end (if earlier than event)
  censor_date <- pmin_date(death_date, study_end)
  # Follow-up end = min(event, censor)
  end_date <- ifelse(ev_valid & (event_date <= censor_date),
                     event_date, censor_date)
  end_date <- as.Date(end_date, origin = "1970-01-01")
  # Status = 1 if event before or on end_date, else 0
  status <- as.integer(ev_valid & !is.na(end_date) & (event_date <= end_date))
  # TTE (days/years) from start to end
  tte_days  <- as.numeric(end_date - start_date)
  tte_years <- tte_days / 365.25
  list(status = status, tte_days = tte_days, tte_years = tte_years, end_date = end_date)
}

# Build survival vars for mortality outcomes:
build_surv_vars_for_death <- function(start_date, event_death_date, other_death_date, study_end) {
  # Event death date valid if > start
  ev_valid <- !is.na(event_death_date) & (event_death_date > start_date)
  censor_date <- pmin_date(other_death_date, study_end)
  # End date = min(event, censor)
  end_date <- ifelse(ev_valid & (event_death_date <= censor_date),
                     event_death_date, censor_date)
  end_date <- as.Date(end_date, origin = "1970-01-01")
  status <- as.integer(ev_valid & !is.na(end_date) & (event_death_date <= end_date))
  tte_days  <- as.numeric(end_date - start_date)
  tte_years <- tte_days / 365.25
  list(status = status, tte_days = tte_days, tte_years = tte_years, end_date = end_date)
}
# EID
stopifnot("f.eid" %in% names(ukb))
setnames(ukb, "f.eid", "eid")

# Baseline (Field 53) — take first non-NA across instances
base_cols <- ukb_cols_for_field(ukb, 53)
stopifnot(length(base_cols) >= 1)
# normalize to Date
for (cc in base_cols) ukb[[cc]] <- suppressWarnings(as.Date(ukb[[cc]]))
ukb$baseline_date <- earliest_date(ukb, base_cols)

# Death date (40000)
death_cols <- ukb_cols_for_field(ukb, 40000)
if (length(death_cols) > 0) {
  for (cc in death_cols) ukb[[cc]] <- suppressWarnings(as.Date(ukb[[cc]]))
  ukb$death_date_allcause <- earliest_date(ukb, death_cols)
} else {
  ukb$death_date_allcause <- as.Date(NA)
}

# Death causes
cod1_cols <- ukb_cols_for_field(ukb, 40001)  # underlying (primary) cause
cod2_cols <- ukb_cols_for_field(ukb, 40002)  # contributory (secondary) causes

# Hospital ICD-10 arrays
icd_codes_cols <- ukb_cols_for_field(ukb, 41270)  # ICD-10 codes
icd_date_cols  <- ukb_cols_for_field(ukb, 41280)  # date of first inpatient ICD10 diagnosis for the code

# 3) ICD-10 definitions by outcome
# Composite CVD: I20–I25 and I60–I64
CVD_PATTS   <- paste0("^I", c(20:25, 60:64))
# MI (I21, I22, I23, I24.1, I25.2) – approximate via I21–I23 + I24 + I25; refine with FO if available
MI_PATTS    <- c("^I21", "^I22", "^I23", "^I24(\\.1)?$", "^I25(\\.2)?$")
# HF
HF_PATTS    <- c("^I50")
# AF
AF_PATTS    <- c("^I48")
# Stroke
STROKE_PATTS <- paste0("^I", 60:64)
# CVD death: I00–I99 in death causes
CVD_MORT_PATTS <- c("^I[0-9]{2}")
# Placebo outcomes
OA_PATTS    <- paste0("^M", 15:19)    # M15–M19
CAT_PATTS   <- paste0("^H", 25:26)    # H25–H26
# 4) First Occurrence (FO) field ID lists
FO_AF_IDS    <- c(131350)
FO_HF_IDS    <- c(131354)
FO_IHD_IDS   <- c(131296,131298,131300,131302,131304,131306)  # I20–I25
FO_STROKE_IDS<- c(131360,131362,131364,131366,131368,131370,131372,131374,131376,131378)
FO_MI_IDS    <- c(131298,131300,131302,131304,131306)  # I21–I25 (含 I24/I25)
# 5) Derive earliest diagnosis dates (prefer FO; fallback to HES arrays)
prefer_FO_else_HES <- function(df, fo_ids, hes_patterns) {
  fo_date <- get_earliest_from_first_occurrence(df, fo_ids)
  hes_date <- get_earliest_from_hes_arrays(df, icd_codes_cols, icd_date_cols, hes_patterns)
  out <- ifelse(!is.na(fo_date), fo_date, hes_date)
  as.Date(out, origin = "1970-01-01")
}
# AF (I48)
ukb$dt_af <- prefer_FO_else_HES(ukb, FO_AF_IDS, AF_PATTS)
# HF (I50)
ukb$dt_hf <- prefer_FO_else_HES(ukb, FO_HF_IDS, HF_PATTS)
# Ischaemic heart disease (I20–I25) – used for CVD composite part
ukb$dt_ihd <- prefer_FO_else_HES(ukb, FO_IHD_IDS, paste0("^I", 20:25))
# Stroke (I60–I64) – for CVD composite part and stroke outcome
fo_stroke_any <- get_earliest_from_first_occurrence(ukb, FO_STROKE_IDS)
hes_stroke    <- get_earliest_from_hes_arrays(ukb, icd_codes_cols, icd_date_cols, STROKE_PATTS)
ukb$dt_stroke <- ifelse(!is.na(fo_stroke_any), fo_stroke_any, hes_stroke) |> as.Date(origin = "1970-01-01")
# MI
fo_mi <- get_earliest_from_first_occurrence(ukb, FO_MI_IDS)
hes_mi <- get_earliest_from_hes_arrays(ukb, icd_codes_cols, icd_date_cols, MI_PATTS)
ukb$dt_mi <- ifelse(!is.na(fo_mi), fo_mi, hes_mi) |> as.Date(origin = "1970-01-01")
# Composite CVD: earliest of (IHD, Stroke)
ukb$dt_cvd <- pmin_date(ukb$dt_ihd, ukb$dt_stroke)
# Placebo: Osteoarthritis & Cataract
ukb$dt_oa       <- get_earliest_from_hes_arrays(ukb, icd_codes_cols, icd_date_cols, OA_PATTS)
ukb$dt_cataract <- get_earliest_from_hes_arrays(ukb, icd_codes_cols, icd_date_cols, CAT_PATTS)
# 6) CVD mortality (I00–I99 in death causes)
death_cause_matches <- function(df, cause_cols1, cause_cols2, pattern_vec) {
  patt <- paste(pattern_vec, collapse = "|")
  # collapse both sets
  any_match <- logical(nrow(df))
  if (length(cause_cols1) > 0) {
    m1 <- apply(df[, ..cause_cols1], 1, function(x) any(grepl(patt, x)))
  } else {
    m1 <- rep(FALSE, nrow(df))
  }
  if (length(cause_cols2) > 0) {
    m2 <- apply(df[, ..cause_cols2], 1, function(x) any(grepl(patt, x)))
  } else {
    m2 <- rep(FALSE, nrow(df))
  }
  any_match <- m1 | m2
  any_match
}
ukb$death_is_cvd <- death_cause_matches(ukb, cod1_cols, cod2_cols, CVD_MORT_PATTS)
# CVD death date = death_date_allcause if cause matches
ukb$dt_cvd_death <- ifelse(ukb$death_is_cvd, ukb$death_date_allcause, as.Date(NA))
ukb$dt_cvd_death <- as.Date(ukb$dt_cvd_death, origin = "1970-01-01")
stopifnot("baseline_date" %in% names(ukb))
# wrapper to add three columns per outcome
add_surv_triplet <- function(df, prefix, event_date_vec, death_date_vec, study_end = STUDY_END) {
  sv <- build_surv_vars(df$baseline_date, event_date_vec, death_date_vec, study_end)
  df[[paste0("ev_", prefix)]]         <- sv$status
  df[[paste0("tte_", prefix, "_days")]]  <- sv$tte_days
  df[[paste0("tte_", prefix, "_years")]] <- round(sv$tte_years, 6)
  df[[paste0("end_", prefix, "_date")]]  <- sv$end_date
  df
}
# For death outcomes (where event is death with specific cause)
add_surv_for_death <- function(df, prefix, event_death_date_vec, allcause_death_date_vec, study_end = STUDY_END) {
  sv <- build_surv_vars_for_death(df$baseline_date, event_death_date_vec, allcause_death_date_vec, study_end)
  df[[paste0("ev_", prefix)]]         <- sv$status
  df[[paste0("tte_", prefix, "_days")]]  <- sv$tte_days
  df[[paste0("tte_", prefix, "_years")]] <- round(sv$tte_years, 6)
  df[[paste0("end_", prefix, "_date")]]  <- sv$end_date
  df
}
# Apply to each outcome
ukb <- add_surv_triplet(ukb, "cvd",      ukb$dt_cvd,      ukb$death_date_allcause)
ukb <- add_surv_triplet(ukb, "mi",       ukb$dt_mi,       ukb$death_date_allcause)
ukb <- add_surv_triplet(ukb, "hf",       ukb$dt_hf,       ukb$death_date_allcause)
ukb <- add_surv_triplet(ukb, "af",       ukb$dt_af,       ukb$death_date_allcause)
ukb <- add_surv_triplet(ukb, "stroke",   ukb$dt_stroke,   ukb$death_date_allcause)
ukb <- add_surv_for_death(ukb, "cvd_death", ukb$dt_cvd_death, ukb$death_date_allcause)
# Placebo outcomes
ukb <- add_surv_triplet(ukb, "oa",        ukb$dt_oa,       ukb$death_date_allcause)
ukb <- add_surv_triplet(ukb, "cataract",  ukb$dt_cataract, ukb$death_date_allcause)

# Negative/zero TTE -> set to NA
tte_cols <- grep("^tte_.*_days$", names(ukb), value = TRUE)
for (cc in tte_cols) {
  bad <- !is.na(ukb[[cc]]) & ukb[[cc]] < 0
  ukb[bad, (cc) := NA]
}
# Years from days
for (nm in grep("^tte_.*_years$", names(ukb), value = TRUE)) {
  days_nm <- sub("_years$", "_days", nm)
  ukb[[nm]] <- round(ukb[[days_nm]] / 365.25, 6)
}
# 10) Save analysis-ready subset (minimal columns)
keep_cols <- c(
  "eid", "baseline_date", "death_date_allcause",
  # event dates
  "dt_cvd","dt_mi","dt_hf","dt_af","dt_stroke","dt_cvd_death","dt_oa","dt_cataract",
  # survival triplets
  grep("^ev_",  names(ukb), value = TRUE),
  grep("^tte_", names(ukb), value = TRUE),
  grep("^end_", names(ukb), value = TRUE)
)

############################################
# Polygenic / Genetic Risk Score for CVD, MI, HF, AF, Stroke 
# (A) Genotype: PLINK prefix (bed/bim/fam). Example: "ukb_chr1_22" if merged.
plink_prefix <- "path/ration/2025/plink_prefix" 
# GWAS weights manifest
weights_path <- "path/to/weights_manifest.csv"  
# Output
out_prefix   <- "grs_ukb_five_traits"
# (D) Filters & options
MAF_MIN        <- 0.01      # exclude SNPs with MAF < 1%
ALLOW_PALIND   <- TRUE      # keep palindromic SNPs if MAF <= 0.4 and resolvable
DROP_DUP_RSIDS <- TRUE      # drop duplicated rsID in weights within a trait
PLOT_QC        <- TRUE

# 1) Read genotype with bigsnpr (PLINK)
# Create a temporary .rds once; afterwards use snp_attach to re-open fast
rds_path <- paste0(plink_prefix, ".rds")
if (!file.exists(rds_path)) {
  message("Converting PLINK to FBM backing file (one-time)...")
  snp_readBed(bedfile = paste0(plink_prefix, ".bed"))
}
obj.big <- snp_attach(rds_path)

G <- obj.big$genotypes            # FBM.code256 matrix of 0/1/2
CHR <- obj.big$map$chromosome     # numeric chromosome
POS <- obj.big$map$physical.pos   # base-pair position
RSID <- obj.big$map$marker.ID     # rsid
A1 <- obj.big$map$allele1         # coded allele in G (usually minor)
A2 <- obj.big$map$allele2         # other allele
sample_ids <- obj.big$fam$sample.ID  
N <- nrow(G); M <- ncol(G)
cat(sprintf("Loaded genotypes: %d individuals x %d variants\n", N, M))
# Build 'info_snp'
info_snp <- data.frame(
  chr = CHR,
  pos = POS,
  rsid = RSID,
  a0 = A2,  # non-effect allele 
  a1 = A1,  # effect allele for dosage coding in G 
  stringsAsFactors = FALSE
)

# 2) Read weights and standardize columns
raw_w <- fread(weights_path)
stopifnot(all(c("trait","rsid","chr","pos","effect_allele","other_allele","weight","weight_type") %in% names(raw_w)))
# Normalize column 
w0 <- raw_w %>%
  mutate(
    trait = as.character(trait),
    chr   = as.integer(chr),
    pos   = as.integer(pos),
    a1    = toupper(effect_allele),
    a0    = toupper(other_allele),
    beta  = ifelse(tolower(weight_type) %in% c("or", "odds_ratio"),
                   log(as.numeric(weight)), as.numeric(weight))
  ) %>%
  select(trait, rsid, chr, pos, a0, a1, beta)

# drop duplicated rsid within the same trait 
if (DROP_DUP_RSIDS) {
  w0 <- w0 %>%
    arrange(trait, rsid, desc(abs(beta))) %>%
    distinct(trait, rsid, .keep_all = TRUE)
}

traits <- c("CVD","MI","HF","AF","Stroke")
if (!all(traits %in% unique(w0$trait))) {
  warning(" missing in weights",
          paste(intersect(traits, unique(w0$trait)), collapse = ", "))
}
traits <- intersect(traits, unique(w0$trait))
# 3) Functions for harmonization and PRS computation
# Wrapper for snp_match with extra controls for palindromic SNPs
match_weights <- function(weights_trait, info_snp, allow_palind = TRUE) {
  mt <- snp_match(sumstats = weights_trait, info_snp = info_snp,
                  strand_flip = TRUE, join_by_pos = FALSE)
  # mt has columns: _NUM_ID_, a0, a1 (harmonized to info_snp$a0/a1),
  #                 beta (flipped as necessary), pos, chr, rsid, etc.
  # Filter palindromic if not allowed or too ambiguous (MAF close to 0.5)
  if (!allow_palind) {
    mt <- mt %>% filter(!(a0 %in% c("A","T") & a1 %in% c("A","T")),
                        !(a0 %in% c("C","G") & a1 %in% c("C","G")))
  }
  return(mt)
}
# Compute MAF for a set of variants (by column indices in G)
get_maf <- function(G, ind.col) {
  # bigsnpr counts 0/1/2; MAF = min(p, 1-p) where p = allele1 frequency
  af <- snp_MAF(G, ind.col = ind.col)  # returns MAF already
  return(af)
}
# Compute PRS = sum( (geno - center) * beta ) + constant
# For simplicity, we compute: sum( dosage_of_effect_allele * beta ).
# Missing genotypes are imputed to 2 * MAF (mean-imputation).
compute_prs <- function(G, matched) {
  ind.col <- matched$`_NUM_ID_`
  betas   <- matched$beta
  # Mean-impute to 2*MAF
  maf <- get_maf(G, ind.col)
  center_vec <- 2 * maf
  # big_prodVec: fast geno * beta with optional centering
  prs <- big_prodVec(G, betas, ind.col = ind.col, center = center_vec, scale = FALSE)
  # Add back mean term so that it's equivalent to sum(geno*beta)
  # sum((g - 2p)*b) = sum(g*b) - sum(2p*b)  => sum(g*b) = prod + sum(2p*b)
  prs <- prs + sum(center_vec * betas)
  as.numeric(prs)
}
# Standardize scores to mean 0, SD 1
zscore <- function(x) {
  m <- mean(x, na.rm = TRUE); s <- sd(x, na.rm = TRUE)
  ifelse(is.finite(s) & s > 0, (x - m)/s, x*NA_real_)
}
# Decile function
decile <- function(x) {
  cut(x, breaks = quantile(x, probs = seq(0,1,0.1), na.rm = TRUE),
      include.lowest = TRUE, labels = paste0("P", 1:10))
}
# 4) Main loop per trait
scores <- list()
kept_snps <- list()

for (tr in traits) {
  cat("\n==\n")
  cat("Trait: ", tr, "\n")
  w_tr <- w0 %>% filter(trait == tr)
  # Harmonize to genotype map
  mt <- match_weights(w_tr, info_snp, allow_palind = ALLOW_PALIND)
  if (nrow(mt) == 0) {
    warning("No matched SNPs for ", tr, "; skipping.")
    next
  }
  # MAF filter 
  maf <- get_maf(G, ind.col = mt$`_NUM_ID_`)
  keep <- maf >= MAF_MIN & is.finite(maf)
  if (!any(keep)) {
    warning("All SNPs filtered by MAF for ", tr)
    next
  }
  mt <- mt[keep, , drop = FALSE]
  
  cat(sprintf("Matched & kept %d SNPs for %s (MAF>=%.2f)\n", nrow(mt), tr, MAF_MIN))
  # Compute PRS
  prs <- compute_prs(G, mt)
  # Save raw and standardized
  scores[[tr]] <- data.frame(
    eid = sample_ids,
    trait = tr,
    prs_raw = prs,
    prs_std = zscore(prs),
    stringsAsFactors = FALSE
  )
  kept_snps[[tr]] <- mt %>% select(trait = tr, rsid, chr, pos, a0, a1, beta)
  
  # Quick QC plot
  if (PLOT_QC) {
    dfp <- scores[[tr]]
    p <- ggplot(dfp, aes(x = prs_std)) +
      geom_histogram(bins = 60, alpha = 0.7) +
      theme_minimal() + labs(title = paste0(tr, " GRS (z-scored)"),
                             x = "Standardized GRS", y = "Count")
    print(p)
  }
}
# Combine all traits
scores_df <- bind_rows(scores)
if (nrow(scores_df) == 0) stop("No scores computed")

# Wide format: one column per trait (standardized)
scores_wide <- scores_df %>%
  select(eid, trait, prs_std) %>%
  pivot_wider(names_from = trait, values_from = prs_std, names_prefix = "GRS_")

# Add deciles per trait
for (tr in traits) {
  col <- paste0("GRS_", tr)
  if (col %in% names(scores_wide)) {
    scores_wide[[paste0(col, "_decile")]] <- decile(scores_wide[[col]])
  }
}

# Correlation matrix among the 5 GRS 
grs_cols <- paste0("GRS_", traits)
grs_cols <- grs_cols[grs_cols %in% names(scores_wide)]
grs_cor <- cor(scores_wide[, grs_cols, drop = FALSE], use = "pairwise.complete")
print(round(grs_cor, 3))

# Save outputs
out_scores_csv <- paste0(out_prefix, "_scores.csv")
fwrite(scores_wide, out_scores_csv)
cat("Saved scores to: ", out_scores_csv, "\n")
# Save kept SNP lists 
out_snps_dir <- paste0(out_prefix, "_snps")
dir.create(out_snps_dir, showWarnings = FALSE)
iwalk(kept_snps, function(df, tr) {
  fn <- file.path(out_snps_dir, paste0("snps_", tr, ".csv"))
  fwrite(df, fn)
})

# Multiple imputation
must_have <- c(
  # exposure / design variables
  "rationed2","birth_place","birth_month","real_food_cpi","survey_year",'household_income','TDI',
  # parental history
  "parent_cvd","parent_diab","parent_htn",
  # early-life covariates
  "maternal_smoke","breastfed",
  # demographics
  "age","sex","eth2",
  # outcomes
  "ev_cvd","ev_mi","ev_hf","ev_af","ev_stroke","ev_cvd_death"
)
missing_must <- setdiff(must_have, names(dat0))
if (length(missing_must) > 0) {
  warning("skipped: ",
          paste(missing_must, collapse = ", "))
  must_have <- intersect(must_have, names(dat0))
}

dat <- dat0 %>% dplyr::select(any_of(must_have))
# Harmonize types 
if ("sex" %in% names(dat) && !is.factor(dat$sex)) dat$sex <- factor(dat$sex)
if ("eth2" %in% names(dat) && !is.factor(dat$eth2)) dat$eth2 <- factor(dat$eth2, levels = c("White","Non-white"))
if ("birth_place" %in% names(dat) && !is.factor(dat$birth_place)) dat$birth_place <- factor(dat$birth_place)
if ("birth_month" %in% names(dat) && !is.factor(dat$birth_month)) dat$birth_month <- factor(dat$birth_month, levels = 1:12)
if ("rationed2" %in% names(dat) && !is.factor(dat$rationed2)) dat$rationed2 <- factor(dat$rationed2, levels = c("Not rationed","Rationed"))
bin_to_factor <- function(x) {
  if (is.numeric(x) && all(na.omit(x) %in% c(0,1))) factor(x, levels = c(0,1), labels = c("No","Yes")) else x
}
for (v in c("parent_cvd","parent_diab","parent_htn","maternal_smoke","breastfed")) {
  if (v %in% names(dat)) dat[[v]] <- bin_to_factor(dat[[v]])
}
message("\n[Missingness overview]")
miss_tbl <- naniar::miss_var_summary(dat) %>% 
  mutate(pct = round(pct_miss, 2)) %>% dplyr::select(variable, n_miss, pct)
print(head(miss_tbl, 20))
message("\n[Little MCAR test] (fail-to-reject => consistent with MCAR)")
#use a numeric-only subset
mcar_sub <- dat %>%
  mutate(across(where(is.factor), ~ as.numeric(.)))  # ok for the test
mcar_res <- naniar::mcar_test(mcar_sub)
print(mcar_res)
#  - Outcomes & exposure -> "" (no imputation)
is_binary_factor <- function(x) is.factor(x) && length(levels(x)) == 2L
is_unordered_factor <- function(x) is.factor(x) && !is.ordered(x) && length(levels(x)) >= 3L
meth <- make.method(dat)

for (nm in names(dat)) {
  x <- dat[[nm]]
  if (nm %in% c("ev_cvd","ev_mi","ev_hf","ev_af","ev_stroke","ev_cvd_death","rationed2")) {
    meth[nm] <- ""  
  } else if (is.numeric(x)) {
    meth[nm] <- "pmm"  
  } else if (is_binary_factor(x)) {
    meth[nm] <- "logreg"
  } else if (is.ordered(x)) {
    meth[nm] <- "polr"
  } else if (is_unordered_factor(x)) {
    meth[nm] <- "polyreg"
  } else {
    meth[nm] <- ""      
  }
}
message("\n[MICE method map]")
print(meth)

# Use quickpred 
exclude_vars <- c("ev_cvd","ev_mi","ev_hf","ev_af","ev_stroke","ev_cvd_death","rationed2")
pred <- quickpred(dat, mincor = 0.05, include = NULL, exclude = exclude_vars)
# Do not let a variable predict itself
diag(pred) <- 0L
# multiple imputation ---------------------------------
imp <- mice(
  dat, m = 20, maxit = 20,
  method = meth,
  predictorMatrix = pred,
  printFlag = TRUE, 
)
message("\n[Trace plots for convergence]")
# Show traces for several representative variables
vars_trace <- c("real_food_cpi","maternal_smoke","breastfed","parent_cvd","birth_month")
vars_trace <- intersect(vars_trace, names(dat))
print(plot(imp, vars = vars_trace))

# Kernel density 
cont_vars <- names(Filter(is.numeric, dat))
if (length(cont_vars)) {
  print(densityplot(imp, ~ get(cont_vars[1])))
}

#FMI (Fraction of Missing Information) 
compute_rvi <- function(fitlist, term) {
  # Extract estimate and SE 
  est <- sapply(fitlist$analyses, function(f) coef(summary(f))[term, "Estimate"])
  se2 <- sapply(fitlist$analyses, function(f) coef(summary(f))[term, "Std. Error"]^2)
  m <- length(est)
  Qbar <- mean(est)
  Ubar <- mean(se2)
  B    <- var(est)
  rvi  <- ((1 + 1/m) * B) / Ubar
  list(Qbar = Qbar, Ubar = Ubar, B = B, RVI = rvi)
}
if (all(c("maternal_smoke") %in% names(dat))) {
  fit_ms <- with(imp, glm(maternal_smoke ~ 1, family = binomial))
  sum_ms <- summary(pool(fit_ms))
  fmi_ms <- sum_ms$fmi[1]  # FMI for intercept
  rvi_ms <- compute_rvi(fit_ms, "(Intercept)")$RVI
  cat("\n[FMI/RVI] Maternal smoking around birth: FMI =",
      round(fmi_ms,3), "; RVI =", round(rvi_ms,3), "\n")
}
if (all(c("breastfed") %in% names(dat))) {
  fit_bf <- with(imp, glm(breastfed ~ 1, family = binomial))
  sum_bf <- summary(pool(fit_bf))
  fmi_bf <- sum_bf$fmi[1]
  rvi_bf <- compute_rvi(fit_bf, "(Intercept)")$RVI
  cat("[FMI/RVI] Breastfed as baby: FMI =", round(fmi_bf,3),
      "; RVI =", round(rvi_bf,3), "\n")
}
#Create completed datasets 
# 7.1 Long/stacked data
dat_long <- complete(imp, action = "long", include = TRUE)  # .imp==0 is original
# 7.2 Single completed dataset
ukb <- complete(imp, 1)
# ======================================================================
# Table 2: Associations of rationing exposure with cardiovascular outcomes
setDT(ukb)
# Real food prices CSV (CPI-adjusted)
prices_csv <- "real_food_prices.csv"  
prices <- fread(prices_csv)
# Normalize the price table
if (!all(c("year","month") %in% names(prices))) {
  if ("date" %in% names(prices)) {
    prices <- prices %>%
      mutate(date = as.Date(date)) %>%
      mutate(year = year(date), month = month(date))
  } else {
    stop("Price ")
  }
}
if (!("real_food_cpi" %in% names(prices))) {
  cand <- setdiff(names(prices), c("year","month","date"))
  stopifnot(length(cand) >= 1)
  setnames(prices, cand[1], "real_food_cpi")
}
prices <- prices %>% select(year, month, real_food_cpi) %>%
  distinct()
# 1) Exposure mapping (birth_group -> 4-category factor)
stopifnot("birth_group" %in% names(ukb))
ukb <- ukb %>%
  mutate(
    exposure4 = case_when(
      birth_group %in% 1:2 ~ "In utero + 1-2 years",
      birth_group %in% 3:4 ~ "In utero + 0-1 year",
      birth_group == 5     ~ "In utero",
      birth_group %in% 6:9 ~ "Not rationed",
      TRUE ~ NA_character_
    ),
    exposure4 = factor(exposure4,
                       levels = c("Not rationed",
                                  "In utero",
                                  "In utero + 0-1 year",
                                  "In utero + 1-2 years"))
  )

# For P-trend
ukb$expo_trend <- as.integer(ukb$exposure4) - 1L  # Not rationed=0 ... +1-2y=3
# 2) Merge real food prices by year of birth
stopifnot(all(c("yob","mob") %in% names(ukb)))
ukb <- ukb %>%
  left_join(prices, by = c("yob" = "year", "mob" = "month")) %>%
  rename(real_food_cpi = real_food_cpi)
ukb <- ukb %>%
  group_by(yob) %>%
  mutate(real_food_cpi = ifelse(is.na(real_food_cpi),
                                mean(real_food_cpi, na.rm = TRUE), real_food_cpi)) %>%
  ungroup()
if (any(is.na(ukb$real_food_cpi))) {
  ukb$real_food_cpi[is.na(ukb$real_food_cpi)] <- mean(ukb$real_food_cpi, na.rm = TRUE)
}
# 3) Covariates
if (!("age" %in% names(ukb))) {
  stopifnot("baseline_date" %in% names(ukb))
  dob_mid <- as.Date(paste0(ukb$yob, "-", ifelse(is.na(ukb$mob), 6, ukb$mob), "-15"))
  ukb$age <- as.numeric(time_length(interval(dob_mid, as.Date(ukb$baseline_date)), "years"))
}
if (!is.factor(ukb$sex)) ukb$sex <- factor(ukb$sex)

if (!is.factor(ukb$ethnicity)) ukb$ethnicity <- factor(ukb$ethnicity)

if (!("birth_place" %in% names(ukb))) {
  stop("Need factor ")
}
if (!is.factor(ukb$birth_place)) ukb$birth_place <- factor(ukb$birth_place)
# Calendar month of birth
ukb$birth_month <- factor(ukb$mob, levels = 1:12)
need_bin <- c("parent_cvd","parent_diab","parent_htn","maternal_smoke","breastfed")
for (v in need_bin) {
  if (!(v %in% names(ukb))) stop(paste("Missing binary covariate:", v))
  ukb[[v]] <- as.integer(ukb[[v]])
}
ukb$survey_year <- year(as.Date(ukb$baseline_date))
outcomes <- tribble(
  ~label, ~time_col,            ~event_col,      ~grs_col,
  "Cardiovascular disease", "tte_cvd_days",      "ev_cvd",      "GRS_CVD",
  "Myocardial infarction",  "tte_mi_days",       "ev_mi",       "GRS_MI",
  "Heart failure",          "tte_hf_days",       "ev_hf",       "GRS_HF",
  "Atrial fibrillation",    "tte_af_days",       "ev_af",       "GRS_AF",
  "Stroke",                 "tte_stroke_days",   "ev_stroke",   "GRS_Stroke"
)
# Count "Total cases / total n" by exposure category
case_count <- function(df, event_col) {
  df %>%
    group_by(exposure4) %>%
    summarise(
      cases = sum(.data[[event_col]] == 1, na.rm = TRUE),
      n     = sum(!is.na(.data[[event_col]]) & !is.na(exposure4))
    ) %>% ungroup()
}
# Format HR 
fmt_hr <- function(hr, lcl, ucl, digits = 2) {
  sprintf("%0.*f (%0.*f to %0.*f)", digits, hr, digits, lcl, digits, ucl)
}
# Extract HR for exposure categories vs reference from coxph
extract_hr_cat <- function(fit, var = "exposure4") {
  sm <- broom::tidy(fit, conf.int = TRUE, exponentiate = TRUE)
  # rows like 'exposure4In utero', etc.
  sm <- sm %>% filter(grepl(paste0("^", var), term))
  transform_row <- function(row) {
    nm <- sub(paste0("^", var), "", row$term)
    nm <- sub("^", "", nm)
    nm
  }
  sm$cat <- sub(paste0(var), "", sm$term)
  sm$cat <- trimws(sm$cat)
  sm %>% select(cat, estimate, conf.low, conf.high, p.value)
}

# Extract HR from Gompertz (flexsurvreg) — coefficients on log-HR scale
extract_hr_gomp <- function(fit, var = "exposure4") {
  sm <- broom::tidy(fit)  # includes coefs and SE on log scale
  sm <- sm %>% filter(grepl(paste0("^", var), term))
  sm$cat <- sub(paste0(var), "", sm$term) %>% trimws()
  sm %>%
    transmute(
      cat = cat,
      estimate = exp(estimate),
      p.value = 2*pnorm(-abs(estimate/std.error))
    )
}
# Cox formula builders
form_m1 <- function(time_col, event_col) {
  as.formula(paste0("Surv(", time_col, ", ", event_col, ") ~ exposure4 + age + sex"))
}
form_m2 <- function(time_col, event_col, grs_col) {
  rhs <- paste(
    "exposure4",
    "age", "sex", "ethnicity", "birth_place", "birth_month",
    "real_food_cpi", "parent_cvd", "parent_diab", "parent_htn",
    grs_col, "maternal_smoke", "breastfed", "survey_year",
    sep = " + "
  )
  as.formula(paste0("Surv(", time_col, ", ", event_col, ") ~ ", rhs))
}
form_trend <- function(time_col, event_col, grs_col) {
  rhs <- paste(
    "expo_trend",
    "age", "sex", "ethnicity", "birth_place", "birth_month",
    "real_food_cpi", "parent_cvd", "parent_diab", "parent_htn",
    grs_col, "maternal_smoke", "breastfed", "survey_year",
    sep = " + "
  )
  as.formula(paste0("Surv(", time_col, ", ", event_col, ") ~ ", rhs))
}

exp_levels <- levels(ukb$exposure4)

make_one_block <- function(df, lab, time_col, event_col, grs_col) {
  dsub <- df %>% filter(!is.na(.data[[time_col]]),
                        !is.na(.data[[event_col]]),
                        !is.na(exposure4),
                        .data[[time_col]] > 0)
  
  cnt <- case_count(dsub, event_col) %>%
    mutate(label = paste0(cases, "/", n)) %>%
    select(exposure4, label)
  cnt_w <- cnt %>% pivot_wider(names_from = exposure4, values_from = label) %>%
    mutate(Row = "Total cases/total sample size") %>%
    select(Row, all_of(exp_levels))
  
  # -------- Model 1 (Cox)
  fit1 <- coxph(form_m1(time_col, event_col), data = dsub, ties = "efron")
  hr1  <- extract_hr_cat(fit1, var = "exposure4")
  hr1_w <- tibble(cat = exp_levels[-1]) %>%   # excluding reference
    left_join(hr1, by = c("cat" = "cat")) %>%
    mutate(hr_txt = fmt_hr(estimate, conf.low, conf.high)) %>%
    select(cat, hr_txt)
  # assemble row
  row_m1 <- tibble(Row = "Model 1",
                   `Not rationed` = "Reference") %>%
    bind_cols(as.list(setNames(hr1_w$hr_txt, hr1_w$cat))) %>%
    # ensure all columns exist
    mutate(`In utero` = coalesce(`In utero`, ""),
           `In utero + 0-1 year` = coalesce(`In utero + 0-1 year`, ""),
           `In utero + 1-2 years` = coalesce(`In utero + 1-2 years`, "")) %>%
    select(Row, all_of(exp_levels))
  # -------- Model 2 (Cox)
  fit2 <- coxph(form_m2(time_col, event_col, grs_col), data = dsub, ties = "efron")
  hr2  <- extract_hr_cat(fit2, var = "exposure4")
  hr2_w <- tibble(cat = exp_levels[-1]) %>%
    left_join(hr2, by = c("cat" = "cat")) %>%
    mutate(hr_txt = fmt_hr(estimate, conf.low, conf.high)) %>%
    select(cat, hr_txt)
  row_m2 <- tibble(Row = "Model 2",
                   `Not rationed` = "Reference") %>%
    bind_cols(as.list(setNames(hr2_w$hr_txt, hr2_w$cat))) %>%
    mutate(`In utero` = coalesce(`In utero`, ""),
           `In utero + 0-1 year` = coalesce(`In utero + 0-1 year`, ""),
           `In utero + 1-2 years` = coalesce(`In utero + 1-2 years`, "")) %>%
    select(Row, all_of(exp_levels))
  # -------- Model 3 (Gompertz)
  form3 <- update(form_m2(time_col, event_col, grs_col), . ~ .)  # same RHS
  fit3 <- flexsurvreg(form3, data = dsub, dist = "gompertz")
  hr3  <- extract_hr_gomp(fit3, var = "exposure4")
  hr3_w <- tibble(cat = exp_levels[-1]) %>%
    left_join(hr3, by = c("cat" = "cat")) %>%
    mutate(hr_txt = fmt_hr(estimate, conf.low, conf.high)) %>%
    select(cat, hr_txt)
  row_m3 <- tibble(Row = "Model 3",
                   `Not rationed` = "Reference") %>%
    bind_cols(as.list(setNames(hr3_w$hr_txt, hr3_w$cat))) %>%
    mutate(`In utero` = coalesce(`In utero`, ""),
           `In utero + 0-1 year` = coalesce(`In utero + 0-1 year`, ""),
           `In utero + 1-2 years` = coalesce(`In utero + 1-2 years`, "")) %>%
    select(Row, all_of(exp_levels))
  # -------- P for trend 
  fit_trend <- coxph(form_trend(time_col, event_col, grs_col), data = dsub, ties = "efron")
  p_trend <- broom::tidy(fit_trend) %>%
    filter(term == "expo_trend") %>% pull(p.value)
  p_trend_txt <- ifelse(is.na(p_trend), "NA",
                        ifelse(p_trend < 0.001, "<0.001", sprintf("%.3f", p_trend)))
  block <- bind_rows(cnt_w, row_m1, row_m2, row_m3) %>%
    mutate(Outcome = lab, .before = 1) %>%
    mutate(`P for trend` = c("-", p_trend_txt, p_trend_txt, p_trend_txt))
  
  block
}
blocks <- pmap(outcomes, ~make_one_block(ukb, lab = ..1, time_col = ..2,
                                         event_col = ..3, grs_col = ..4))
tbl_all <- bind_rows(blocks)

###############################Cubic spline
prices_csv <- "real_food_prices.csv"
stopifnot(file.exists(prices_csv))
prices <- fread(prices_csv)

if (!all(c("year","month") %in% names(prices))) {
  if ("date" %in% names(prices)) {
    prices <- prices %>%
      mutate(date = as.Date(date)) %>%
      mutate(year = year(date), month = month(date))
  } else stop("Price CSV must contain (year, month) or a 'date' column.")
}
if (!("real_food_cpi" %in% names(prices))) {
  # If the value column is named differently, take the first non-(year,month,date)
  val_col <- setdiff(names(prices), c("year","month","date"))[1]
  setnames(prices, val_col, "real_food_cpi")
}
prices <- prices %>% select(year, month, real_food_cpi) %>% distinct()

# 1) Exposure variable: months since rationing ended (continuous)
if (!("exposure_months" %in% names(ukb))) {
  stopifnot("birth_group" %in% names(ukb))
  map_months <- c(`1`= 24, `2`= 18, `3`= 12, `4`=  6,
                  `5`=  0, `6`= -9, `7`= -15, `8`= -21, `9`= -27)
  ukb$exposure_months <- unname(map_months[ as.character(ukb$birth_group) ])
}
axis_labels <- c("+24","+18","+12","+6","In utero","-9","-15","-21","≤-21")

# 2) Merge real food prices by year/month of birth
stopifnot(all(c("yob","mob") %in% names(ukb)))
ukb <- ukb %>% left_join(prices, by = c("yob"="year","mob"="month"))
# Impute missing prices with year mean, then overall mean
ukb <- ukb %>%
  group_by(yob) %>%
  mutate(real_food_cpi = ifelse(is.na(real_food_cpi),
                                mean(real_food_cpi, na.rm = TRUE),
                                real_food_cpi)) %>%
  ungroup()
if (any(is.na(ukb$real_food_cpi))) {
  ukb$real_food_cpi[is.na(ukb$real_food_cpi)] <- mean(ukb$real_food_cpi, na.rm = TRUE)
}
# 3) Covariates 
# Age at baseline
if (!("age" %in% names(ukb))) {
  stopifnot("baseline_date" %in% names(ukb))
  dob_mid <- as.Date(paste0(ukb$yob, "-", ifelse(is.na(ukb$mob), 6, ukb$mob), "-15"))
  ukb$age <- as.numeric(time_length(interval(dob_mid, as.Date(ukb$baseline_date)), "years"))
}
if (!is.factor(ukb$sex))       ukb$sex       <- factor(ukb$sex)
if (!is.factor(ukb$ethnicity)) ukb$ethnicity <- factor(ukb$ethnicity)
if (!("birth_place" %in% names(ukb))) stop("Need 'birth_place' (England/Wales/Scotland).")
if (!is.factor(ukb$birth_place)) ukb$birth_place <- factor(ukb$birth_place)
ukb$birth_month <- factor(ukb$mob, levels = 1:12)
ukb$survey_year <- year(as.Date(ukb$baseline_date))
# Binary covariates -> integer
bin_names <- c("parent_cvd","parent_diab","parent_htn","maternal_smoke","breastfed")
for (v in bin_names) if (v %in% names(ukb)) ukb[[v]] <- as.integer(ukb[[v]])
# 4) Outcomes list
outcomes <- tribble(
  ~label,                  ~time_col,              ~event_col,        ~grs_col,
  "Cardiovascular disease","tte_cvd_days",         "ev_cvd",          "GRS_CVD",
  "Myocardial infarction", "tte_mi_days",          "ev_mi",           "GRS_MI",
  "Heart failure",         "tte_hf_days",          "ev_hf",           "GRS_HF",
  "Atrial fibrillation",   "tte_af_days",          "ev_af",           "GRS_AF",
  "Stroke",                "tte_stroke_days",      "ev_stroke",       "GRS_Stroke",
  "CVD mortality",         "tte_cvd_death_days",   "ev_cvd_death",    "GRS_CVD"
)
# 5)  (flexsurv + spline)
# Build Gompertz formula with RCS on exposure (df knots adjustable)
gompertz_formula <- function(time_col, event_col, grs_col, df_spline = 4) {
  rhs <- paste(
    sprintf("ns(exposure_months, df=%d)", df_spline),
    "age", "sex", "ethnicity", "birth_place", "birth_month",
    "real_food_cpi", "parent_cvd", "parent_diab", "parent_htn",
    grs_col, "maternal_smoke", "breastfed", "survey_year",
    sep = " + "
  )
  as.formula(paste0("Surv(", time_col, ", ", event_col, ") ~ ", rhs))
}

typical_row <- function(df, covars) {
  out <- list()
  for (v in covars) {
    x <- df[[v]]
    if (is.numeric(x)) {
      out[[v]] <- median(x, na.rm = TRUE)
    } else if (is.factor(x)) {
      lv <- names(which.max(table(x)))
      out[[v]] <- factor(lv, levels = levels(x))
    } else {
      out[[v]] <- x[which(!is.na(x))[1]]
    }
  }
  as.data.frame(out)
}
# Extract 'rate' coefficients and covariance from flexsurvreg
get_rate_coef <- function(fit) {
  cf <- coef(fit)  # 
  nm_rate <- grep("^rate_", names(cf), value = TRUE)
  beta <- cf[nm_rate]
  V <- vcov(fit)
  V <- V[nm_rate, nm_rate, drop = FALSE]
  list(beta = beta, V = V, names = nm_rate)
}
# Build model matrix with column names matching "rate_*"
model_matrix_rate <- function(fit, newdata) {
  mm <- model.matrix(delete.response(terms(fit)), newdata = newdata)
  colnames(mm) <- paste0("rate_", colnames(mm))
  # Keep columns that appear in rate coefficients
  cf <- coef(fit); nm_rate <- grep("^rate_", names(cf), value = TRUE)
  mm <- mm[, nm_rate, drop = FALSE]
  mm
}
# HR curve vs a reference x0 using contrast of linear predictors
hr_curve_flexsurv <- function(fit, xgrid, x0, base_row) {
  # base_row should include all covariates appearing in formula EXCEPT exposure_months
  base_ref <- base_row; base_ref$exposure_months <- x0
  nr <- length(xgrid)
  base_new <- base_row[rep(1, nr), , drop = FALSE]
  base_new$exposure_months <- xgrid
  
  X  <- model_matrix_rate(fit, base_new)
  Xr <- model_matrix_rate(fit, base_ref)
  
  B <- get_rate_coef(fit)
  beta <- B$beta; V <- B$V
  
  D  <- sweep(X, 2, as.numeric(Xr), FUN = "-")   # contrasts
  lp <- as.numeric(D %*% beta)
  se <- sqrt(rowSums((D %*% V) * D))
  
  tibble(x = xgrid,
         hr  = exp(lp),
         lcl = exp(lp - 1.96*se),
         ucl = exp(lp + 1.96*se))
}
# Nonlinearity p-value: spline vs linear Gompertz (likelihood ratio)
p_nonlinear <- function(df, time_col, event_col, grs_col, df_spline = 4) {
  f_lin <- as.formula(paste0("Surv(", time_col, ", ", event_col, ") ~ ",
                             "exposure_months + ",
                             "age + sex + ethnicity + birth_place + birth_month + ",
                             "real_food_cpi + parent_cvd + parent_diab + parent_htn + ",
                             grs_col, " + maternal_smoke + breastfed + survey_year"))
  f_spl <- gompertz_formula(time_col, event_col, grs_col, df_spline = df_spline)
  fit_lin <- flexsurvreg(f_lin, data = df, dist = "gompertz")
  fit_spl <- flexsurvreg(f_spl, data = df, dist = "gompertz")
  ll1 <- fit_lin$loglik; k1 <- length(coef(fit_lin))
  ll2 <- fit_spl$loglik; k2 <- length(coef(fit_spl))
  pchisq(2*(ll2-ll1), df = (k2-k1), lower.tail = FALSE)
}
# 6) Build curves for all outcomes
spline_df   <- 4      # number of spline degrees of freedom
x_min       <- -27    # left boundary (≤ -21)
x_max       <-  24    # right boundary (+24)
x_grid      <- seq(x_min, x_max, by = 0.5)
ref_x       <- 0      # "In utero" reference (dashed vertical line)
# Covariates needed in formula 
covars_needed <- c("age","sex","ethnicity","birth_place","birth_month",
                   "real_food_cpi","parent_cvd","parent_diab","parent_htn",
                   "maternal_smoke","breastfed","survey_year")
build_panel <- function(df, lab, time_col, event_col, grs_col) {
  dsub <- df %>%
    filter(!is.na(exposure_months),
           !is.na(.data[[time_col]]),
           !is.na(.data[[event_col]]),
           .data[[time_col]] > 0)
  if (!(grs_col %in% names(dsub))) dsub[[grs_col]] <- NA_real_
  # Fit Gompertz with spline
  form <- gompertz_formula(time_col, event_col, grs_col, df_spline = spline_df)
  fit  <- flexsurvreg(form, data = dsub, dist = "gompertz")
  base <- typical_row(dsub, unique(covars_needed, grs_col))
  curve <- hr_curve_flexsurv(fit, x_grid, ref_x, base)
  # P for nonlinearity
  p_nl <- tryCatch(p_nonlinear(dsub, time_col, event_col, grs_col, df_spline),
                   error = function(e) NA_real_)
  curve %>% mutate(outcome = lab, p_nl = p_nl)
}

curves <- pmap(outcomes,
               ~build_panel(ukb, lab = ..1, time_col = ..2, event_col = ..3, grs_col = ..4)) %>%
  bind_rows()
# 7) Plot (2 x 3 facets), English annotations
breaks_months <- c(24,18,12,6,0,-9,-15,-21,-27)
label_months  <- axis_labels
# Prepare "P for nonlinearity" annotation per panel
ann_df <- curves %>%
  group_by(outcome) %>%
  summarise(p = first(p_nl), .groups = "drop") %>%
  mutate(p_lab = ifelse(is.na(p), "P for nonlinearity = NA",
                        ifelse(p < 0.001, "P for nonlinearity <0.001",
                               paste0("P for nonlinearity = ",
                                      scales::number(p, accuracy = 0.001)))),
         x = min(breaks_months) + 2,
         y = min(curves$lcl[curves$outcome == first(outcome)], na.rm = TRUE) + 0.02)
# Draw
p <- ggplot(curves, aes(x = x, y = hr)) +
  geom_ribbon(aes(ymin = lcl, ymax = ucl), alpha = 0.2) +
  geom_line(linewidth = 1) +
  geom_hline(yintercept = 1, linewidth = 0.4) +
  geom_vline(xintercept = ref_x, linetype = "dashed", linewidth = 0.4) +
  scale_x_continuous("Exposure to rationing (months)",
                     breaks = breaks_months, labels = label_months,
                     limits = c(x_min, x_max)) +
  scale_y_continuous("Hazard ratio (95% CI)", limits = c(0.4, NA)) +
  facet_wrap(~ outcome, ncol = 2, scales = "fixed") +
  theme_minimal(base_size = 12) +
  theme(
    panel.grid.minor = element_blank(),
    strip.text = element_text(face = "bold", size = 12),
    axis.title = element_text(size = 11),
    axis.text = element_text(size = 10)
  ) +
  geom_text(data = ann_df, aes(x = x, y = y, label = p_lab),
            inherit.aes = FALSE, hjust = 0, vjust = 0, size = 3.4)

print(p)

# Hazard ratios by date of birth in contemporaneous controls (born outside UK)
if (!("birth_place" %in% names(ukb))) stop("Need 'birth_place' factor.")
if (!is.factor(ukb$birth_place)) ukb$birth_place <- factor(ukb$birth_place)
ukb$outside_uk <- !as.character(ukb$birth_place) %in% c("England","Wales","Scotland")
# Decimal date-of-birth (year + month_center/12)
ukb$dob_decimal <- ukb$yob + (ifelse(is.na(ukb$mob), 6, ukb$mob) - 0.5)/12
ukb$birth_month <- factor(ukb$mob, levels = 1:12)
ukb$survey_year <- year(as.Date(ukb$baseline_date))
#  Focusing window: Oct 1951 to Mar 1956 (inclusive), same as paper.
# -----------------------------
in_window <- with(ukb, (yob > 1951 & yob < 1956) |
                    (yob == 1951 & mob >= 10) |
                    (yob == 1956 & mob <= 3))
ctrl_pool <- ukb %>%
  filter(outside_uk, in_window, !is.na(sex), !is.na(eth2), !is.na(age))
# -----------------------------
ctrl_pool <- ctrl_pool %>%
  mutate(age_band = cut(age, breaks = seq(floor(min(age, na.rm=TRUE)),
                                          ceiling(max(age, na.rm=TRUE)), by = 1),
                        include.lowest = TRUE, right = FALSE))
balanced_sample <- function(df, strata_vars, N_total) {
  tab <- df %>% count(across(all_of(strata_vars)), name = "avail")
  k <- nrow(tab)
  base_n <- floor(N_total / k)
  tab$take <- pmin(tab$avail, base_n)
  rem <- N_total - sum(tab$take)
  if (rem > 0) {
    ord <- order(-tab$avail)
    i <- 1
    while (rem > 0 && any(tab$take < tab$avail)) {
      idx <- ord[i]
      if (tab$take[idx] < tab$avail[idx]) {
        tab$take[idx] <- tab$take[idx] + 1
        rem <- rem - 1
      }
      i <- ifelse(i == k, 1, i + 1)
    }
  }
  parts <- vector("list", nrow(tab))
  for (ii in seq_len(nrow(tab))) {
    ss <- tab[ii, ]
    dss <- df %>%
      filter(across(all_of(strata_vars),
                    ~ .x == ss[[cur_column()]]))
    n_take <- ss$take
    if (n_take > 0) {
      set.seed(2025)
      parts[[ii]] <- dss %>% slice_sample(n = n_take)
    }
  }
  bind_rows(parts)
}
ext_ctrl <- balanced_sample(ctrl_pool, c("sex","eth2","age_band"),
                            N_total = min(N_target, nrow(ctrl_pool)))
cat("External contemporaneous controls sampled: ", nrow(ext_ctrl), "\n")
# Gompertz + spline on DOB
gompertz_formula <- function(time_col, event_col, df_spline = 4) {
  as.formula(paste0(
    "Surv(", time_col, ", ", event_col, ") ~ ",
    "ns(dob_decimal, df=", df_spline, ") + ",
    "age + sex + eth2 + birth_month + survey_year"
  ))
}
get_rate_coef <- function(fit) {
  cf <- coef(fit)
  nm_rate <- grep("^rate_", names(cf), value = TRUE)
  beta <- cf[nm_rate]
  V <- vcov(fit)[nm_rate, nm_rate, drop = FALSE]
  list(beta = beta, V = V, names = nm_rate)
}
# Build model
model_matrix_rate <- function(fit, newdata) {
  mm <- model.matrix(delete.response(terms(fit)), newdata = newdata)
  colnames(mm) <- paste0("rate_", colnames(mm))
  nm_rate <- grep("^rate_", names(coef(fit)), value = TRUE)
  mm[, nm_rate, drop = FALSE]
}
# HR curve vs a reference 
hr_curve_vs_ref <- function(fit, xgrid, xref, base_row) {
  base_ref <- base_row; base_ref$dob_decimal <- xref
  newdata <- base_row[rep(1, length(xgrid)), , drop = FALSE]
  newdata$dob_decimal <- xgrid
  X  <- model_matrix_rate(fit, newdata)
  Xr <- model_matrix_rate(fit, base_ref)
  D  <- sweep(X, 2, as.numeric(Xr), FUN = "-")
  B <- get_rate_coef(fit); beta <- B$beta; V <- B$V
  lp <- as.numeric(D %*% beta)
  se <- sqrt(rowSums((D %*% V) * D))
  tibble(x = xgrid, hr = exp(lp),
                  )
}

# P for nonlinearity 
p_nonlinear <- function(df, time_col, event_col, df_spline = 4) {
  f_lin <- as.formula(paste0("Surv(", time_col, ", ", event_col, ") ~ ",
                             "dob_decimal + age + sex + eth2 + birth_month + survey_year"))
  f_spl <- gompertz_formula(time_col, event_col, df_spline)
  fit0 <- flexsurvreg(f_lin, data = df, dist = "gompertz")
  fit1 <- flexsurvreg(f_spl, data = df, dist = "gompertz")
  pchisq(2*(fit1$loglik - fit0$loglik),
         df = length(coef(fit1)) - length(coef(fit0)), lower.tail = FALSE)
}
typical_row <- function(df) {
  list(
    age = median(df$age, na.rm = TRUE),
    sex = factor(names(which.max(table(df$sex))), levels = levels(df$sex)),
    eth2 = factor(names(which.max(table(df$eth2))), levels = levels(df$eth2)),
    birth_month = factor(names(which.max(table(df$birth_month))),
                         levels = levels(df$birth_month)),
    survey_year = median(df$survey_year, na.rm = TRUE)
  ) %>% as.data.frame()
}
# 4) Outcomes 
outcomes <- tribble(
  ~panel, ~label,                  ~time_col,            ~event_col,
  "(A)",  "CVD",                   "tte_cvd_days",       "ev_cvd",
  "(B)",  "MI",                    "tte_mi_days",        "ev_mi",
  "(C)",  "HF",                    "tte_hf_days",        "ev_hf",
  "(D)",  "AF",                    "tte_af_days",        "ev_af",
  "(E)",  "Stroke",                "tte_stroke_days",    "ev_stroke",
  "(F)",  "CVD mortality",         "tte_cvd_death_days", "ev_cvd_death"
)
# Grid for DOB 
x_min <- 1951 + (10-0.5)/12   # 1951.10
x_max <- 1956 + ( 3-0.5)/12   # 1956.03
x_grid <- seq(x_min, x_max, by = 0.02)

build_panel <- function(df, pan, lab, tcol, ecol) {
  dsub <- df %>%
    filter(!is.na(.data[[tcol]]), !is.na(.data[[ecol]])) %>%
    mutate(time = .data[[tcol]]/365.25,
           event = .data[[ecol]]) %>%
    filter(time > 0)
  # Fit Gompertz with spline on DOB
  form <- gompertz_formula("time","event", df_spline = 4)
  fit  <- flexsurvreg(form, data = dsub, dist = "gompertz")
  base <- typical_row(dsub)
  curve <- hr_curve_vs_ref(fit, x_grid, ref_dob, base)
  
  # Nonlinearity p-value
  p_nl <- p_nonlinear(dsub, "time","event", df_spline = 4)
  p_lab <- ifelse(p_nl < 0.001, "P for nonlinearity < 0.001",
                  paste0("P for nonlinearity = ", number(p_nl, accuracy = 0.001)))
  
  curve %>% mutate(panel = pan, outcome = lab, p_lab = p_lab)
}

curves <- pmap(outcomes,
               ~build_panel(ext_ctrl, ..1, ..2, ..3, ..4)) %>% bind_rows()
# 5) Plotting
# Axis label positions as in figure 
breaks_dob <- c(
  1952.00,  # 1951.10-1952.3
  1952.75,  # 1952.4-1953.3
  1953.50,  # 1953.4-1953.9
  ref_dob,  # 1953.10-1954.6 (vertical dashed)
  1955.00,  # 1954.7-1955.6
  1955.75,  # 1955.7-1955.12
  1956.125  # 1956.1-3
)
labels_dob <- c("1951.10\n-1952.3",
                "1952.4\n-1953.3",
                "1953.4\n-1953.9",
                "1953.10\n-1954.6",
                "1954.7\n-1955.6",
                "1955.7\n-1955.12",
                "1956.1\n-3")
# Annotation positions 
ann_df <- curves %>%
  group_by(panel, outcome) %>%
  summarise(p_lab = first(p_lab), .groups = "drop") %>%
  mutate(x = x_min + 0.02, y = min(curves$lcl, na.rm = TRUE) + 0.05)
p <- ggplot(curves, aes(x = x, y = hr)) +
  geom_ribbon(aes(ymin = lcl, ymax = ucl), fill = "grey70", alpha = 0.6) +
  geom_line(size = 0.8, color = "black") +
  geom_hline(yintercept = 1, linetype = "dotted", color = "red3") +
  geom_vline(xintercept = ref_dob, linetype = "dashed") +
  scale_x_continuous("Date of birth",
                     limits = c(x_min, x_max),
                     breaks = breaks_dob,
                     labels = labels_dob,
                     expand = expansion(add = 0.01)) +
  scale_y_continuous("Hazard ratio", limits = c(0.4, NA)) +
  facet_wrap(~ panel + outcome, ncol = 3, scales = "fixed") +
  theme_minimal(base_size = 12) +
  theme(
    strip.text = element_text(face = "bold"),
    panel.grid.minor = element_blank()
  ) +
  geom_text(data = ann_df,
            aes(x = x_min + 0.02, y = 0.45, label = p_lab),
            inherit.aes = FALSE, hjust = 0, vjust = 0, size = 3.6)

print(p)

#############Fig 4

# In utero vs Not rationed
if (!("exposure_inutero" %in% names(ukb))) {
  stopifnot("birth_group" %in% names(ukb))
  ukb[, exposure4 := factor(case_when(
    birth_group %in% 6:9 ~ "Not rationed",
    birth_group == 5     ~ "In utero",
    birth_group %in% 3:4 ~ "In utero + 0-1 year",
    birth_group %in% 1:2 ~ "In utero + 1-2 years",
    TRUE ~ NA_character_
  ), levels = c("Not rationed","In utero","In utero + 0-1 year","In utero + 1-2 years"))]
  ukb[, exposure_inutero := ifelse(exposure4 == "In utero", 1L,
                                   ifelse(exposure4 == "Not rationed", 0L, NA_integer_))]
}
ukb[, exposure_inutero := as.integer(exposure_inutero)]
ukb_sub <- ukb %>% filter(exposure_inutero %in% c(0L,1L))

if (!("age" %in% names(ukb_sub))) {
  stopifnot(all(c("yob","mob","baseline_date") %in% names(ukb_sub)))
  dob_mid <- as.Date(paste0(ukb_sub$yob, "-", ifelse(is.na(ukb_sub$mob), 6, ukb_sub$mob), "-15"))
  ukb_sub$age <- as.numeric(time_length(interval(dob_mid, as.Date(ukb_sub$baseline_date)), "years"))
}
if (!is.factor(ukb_sub$sex))        ukb_sub$sex        <- factor(ukb_sub$sex)
if (!is.factor(ukb_sub$ethnicity))  ukb_sub$ethnicity  <- factor(ukb_sub$ethnicity)
if (!is.factor(ukb_sub$birth_place))ukb_sub$birth_place<- factor(ukb_sub$birth_place)
ukb_sub$birth_month <- factor(ukb_sub$mob, levels = 1:12)
if (!("survey_year" %in% names(ukb_sub))) ukb_sub$survey_year <- year(as.Date(ukb_sub$baseline_date))

bin_vars <- c("parent_cvd","parent_diab","parent_htn","maternal_smoke","breastfed")
for (v in bin_vars) if (v %in% names(ukb_sub)) ukb_sub[[v]] <- as.integer(ukb_sub[[v]])
stopifnot("real_food_cpi" %in% names(ukb_sub))
# Place of birth：England vs Wales+Scotland 
ukb_sub <- ukb_sub %>%
  mutate(pob2 = case_when(
    birth_place == "England" ~ "England",
    birth_place %in% c("Wales","Scotland") ~ "Wales or Scotland",
    TRUE ~ NA_character_
  )) %>%
  mutate(pob2 = factor(pob2, levels = c("England","Wales or Scotland")))
# Ethnicity：White vs Non-white
ukb_sub <- ukb_sub %>%
  mutate(eth2 = ifelse(as.character(ethnicity) == "White", "White", "Non-white")) %>%
  mutate(eth2 = factor(eth2, levels = c("White","Non-white")))
# 1)  GRS 
outcomes <- tribble(
  ~outcome, ~time_col,            ~event_col,       ~grs_col,      ~prs_label,
  "Cardiovascular disease","tte_cvd_days",          "ev_cvd",      "GRS_CVD",    "PRS for CVD",
  "Myocardial infarction", "tte_mi_days",           "ev_mi",       "GRS_MI",     "PRS for MI",
  "Heart failure",         "tte_hf_days",           "ev_hf",       "GRS_HF",     "PRS for HF",
  "Atrial fibrillation",   "tte_af_days",           "ev_af",       "GRS_AF",     "PRS for AF",
  "Stroke",                "tte_stroke_days",       "ev_stroke",   "GRS_Stroke", "PRS for Stroke",
  "CVD mortality",         "tte_cvd_death_days",    "ev_cvd_death","GRS_CVD",    "PRS for CVD mortality"
)
mk_prs_tertile <- function(df, grs_col) {
  x <- df[[grs_col]]
  if (all(is.na(x))) return(factor(NA_character_))
  qs <- quantile(x, probs = c(1/3, 2/3), na.rm = TRUE, names = FALSE)
  cut(x, breaks = c(-Inf, qs, Inf),
      labels = c("Low","Medium","High"), include.lowest = TRUE, right = TRUE)
}
rhs_base <- c("exposure_inutero",      # （In utero vs Not）
              "age","sex","eth2","pob2","birth_month",
              "real_food_cpi","parent_cvd","parent_diab","parent_htn",
              "maternal_smoke","breastfed","survey_year")
make_formula <- function(time_col, event_col, grs_col, extra_remove = NULL, interaction = NULL) {
  rhs <- rhs_base
  rhs <- c(setdiff(rhs, extra_remove), grs_col)   #  GRS
  rhs <- rhs[!duplicated(rhs)]
  rhs <- paste(rhs, collapse = " + ")
  if (!is.null(interaction)) {
    rhs <- paste(rhs, "+", paste0("exposure_inutero:", interaction))
  }
  as.formula(paste0("Surv(", time_col, ", ", event_col, ") ~ ", rhs))
}

fit_within_level <- function(d, time_col, event_col, grs_col, drop_cov = NULL) {
  f <- make_formula(time_col, event_col, grs_col, extra_remove = drop_cov)
  fit <- flexsurvreg(f, data = d, dist = "gompertz")
  # rate_ 
  sm <- broom::tidy(fit)
  row <- sm %>% filter(term == "rate_exposure_inutero")
  tibble(
    hr  = exp(row$estimate),
    lcl = exp(row$estimate - 1.96*row$std.error),
    ucl = exp(row$estimate + 1.96*row$std.error)
  )
}
# （LRT）
p_interaction <- function(d, time_col, event_col, grs_col, strat_var) {
  f0 <- make_formula(time_col, event_col, grs_col, extra_remove = strat_var, interaction = NULL)
  f1 <- make_formula(time_col, event_col, grs_col, extra_remove = NULL, interaction = strat_var)
  fit0 <- flexsurvreg(f0, data = d, dist = "gompertz")
  fit1 <- flexsurvreg(f1, data = d, dist = "gompertz")
  ll0 <- fit0$loglik; k0 <- length(coef(fit0))
  ll1 <- fit1$loglik; k1 <- length(coef(fit1))
  pchisq(2*(ll1-ll0), df = (k1-k0), lower.tail = FALSE)
}
strata_def <- tribble(
  ~strata_name,        ~var_expr,      ~levels,                                ~drop_cov,
  "Sex",               "sex",          c("Male","Female"),                     "sex",
  "Ethnicity",         "eth2",         c("White","Non-white"),                 "eth2",
  "Place of birth",    "pob2",         c("England","Wales or Scotland"),       "pob2",
  # PRS 
  "PRS tertile",       "prs_tertile",  c("Low","Medium","High"),               "prs_tertile",
  "Parents with diagnosis of CVD",  "parent_cvd_fac", c("No","Yes"),           "parent_cvd_fac",
  "Parents with diagnosis of diabetes","parent_diab_fac",c("No","Yes"),        "parent_diab_fac",
  "Parents with diagnosis of hypertension","parent_htn_fac",c("No","Yes"),     "parent_htn_fac"
)

res_list <- list()
for (i in seq_len(nrow(outcomes))) {
  oc   <- outcomes$outcome[i]
  tcol <- outcomes$time_col[i]
  ecol <- outcomes$event_col[i]
  gcol <- outcomes$grs_col[i]
  prs_lab <- outcomes$prs_label[i]
  
  d0 <- ukb_sub %>%
    filter(!is.na(.data[[tcol]]), !is.na(.data[[ecol]]),
           !is.na(exposure_inutero), .data[[tcol]] > 0)
  
  #  GRS 
  d0$prs_tertile <- mk_prs_tertile(d0, gcol)
  d0$parent_cvd_fac  <- factor(ifelse(d0$parent_cvd==1, "Yes","No"), levels = c("No","Yes"))
  d0$parent_diab_fac <- factor(ifelse(d0$parent_diab==1,"Yes","No"), levels = c("No","Yes"))
  d0$parent_htn_fac  <- factor(ifelse(d0$parent_htn==1, "Yes","No"), levels = c("No","Yes"))
  #  Pinteraction
  for (j in seq_len(nrow(strata_def))) {
    sname <- strata_def$strata_name[j]
    svar  <- strata_def$var_expr[j]
    levs  <- strata_def$levels[[j]]
    dropc <- strata_def$drop_cov[j]
    if (!(svar %in% names(d0))) next
    if (all(is.na(d0[[svar]]))) next
    # interaction P
    p_int <- tryCatch(p_interaction(d0, tcol, ecol, gcol, strat_var = svar),
                      error = function(e) NA_real_)
    #  HR
    for (lv in levs) {
      d_lv <- d0 %>% filter(.data[[svar]] == lv)
      ev_n <- sum(d_lv[[ecol]] == 1, na.rm = TRUE)
      n_n  <- nrow(d_lv)
      if (ev_n < 5 || n_n < 50) {
        hr <- lcl <- ucl <- NA_real_
      } else {
        fit_res <- tryCatch(
          fit_within_level(d_lv, tcol, ecol, gcol, drop_cov = dropc),
          error = function(e) tibble(hr = NA_real_, lcl = NA_real_, ucl = NA_real_)
        )
        hr  <- fit_res$hr; lcl <- fit_res$lcl; ucl <- fit_res$ucl
      }
      
      res_list[[length(res_list) + 1]] <- tibble(
        outcome = oc,
        strata  = sname,
        level   = lv,
        hr = hr, lcl = lcl, ucl = ucl,
        events = ev_n, n = n_n,
        p_interaction = p_int,
        prs_label = prs_lab
      )
    }
  }
}

res <- bind_rows(res_list)
# “PRS tertile”
res <- res %>%
  mutate(strata = ifelse(strata == "PRS tertile", prs_label, strata))
# P 
p_ann <- res %>%
  group_by(outcome, strata) %>%
  summarise(p = first(p_interaction), .groups = "drop") %>%
  mutate(p_txt = case_when(
    is.na(p) ~ "P for interaction = NA",
    p < 0.001 ~ "P for interaction <0.001",
    TRUE ~ paste0("P for interaction = ", number(p, accuracy = 0.001))
  ))
strata_order <- c("Sex","Ethnicity","Place of birth",
                  "PRS for CVD","PRS for MI","PRS for HF","PRS for AF","PRS for Stroke","PRS for CVD mortality",
                  "Parents with diagnosis of CVD",
                  "Parents with diagnosis of diabetes",
                  "Parents with diagnosis of hypertension")
strata_order_used <- strata_order[strata_order %in% unique(res$strata)]

res <- res %>%
  mutate(strata = factor(strata, levels = strata_order_used)) %>%
  arrange(outcome, strata)
# strata
add_separators <- function(df) {
  out <- list()
  for (oc in unique(df$outcome)) {
    df_oc <- df %>% filter(outcome == oc)
    for (st in unique(df_oc$strata)) {
      block <- df_oc %>% filter(strata == st)
      out[[length(out)+1]] <- block
      sep <- tibble(outcome = oc, strata = st, level = " ", hr = NA_real_, lcl = NA_real_, ucl = NA_real_,
                    events = NA_integer_, n = NA_integer_, p_interaction = NA_real_, prs_label = unique(block$prs_label))
      out[[length(out)+1]] <- sep
    }
  }
  bind_rows(out)
}
res_sep <- add_separators(res)
# "<Strata>: <Level>"
res_sep <- res_sep %>%
  mutate(y_label = ifelse(level == " ", paste0(as.character(strata), ":"), paste0("  ", level)))

x_min <- 0.5; x_max <- 2.0
# y_label
res_sep <- res_sep %>%
  group_by(outcome) %>%
  mutate(y_ord = rev(row_number())) %>%
  ungroup()
p_ann_pos <- res_sep %>%
  group_by(outcome, strata) %>%
  summarise(y = max(y_ord, na.rm = TRUE), .groups = "drop") %>%
  group_by(outcome) %>%
  summarise(y = max(y), .groups = "drop") %>%
  left_join(p_ann %>% group_by(outcome) %>% summarise(p_txt = paste0(unique(p_txt), collapse = " | "), .groups = "drop"),
            by = "outcome")
g <- ggplot(res_sep, aes(x = hr, y = y_ord)) +
  geom_vline(xintercept = 1, linetype = "solid", linewidth = 0.4) +
  geom_errorbarh(aes(xmin = lcl, xmax = ucl), height = 0.15, alpha = 0.8,
                 na.rm = TRUE) +
  geom_point(size = 2.2, na.rm = TRUE) +
  scale_x_continuous("Hazard ratio (95% CI)", limits = c(x_min, x_max),
                     breaks = c(0.5, 0.8, 1.0, 1.2, 1.5, 2.0)) +
  scale_y_continuous(NULL, breaks = res_sep$y_ord, labels = res_sep$y_label) +
  facet_wrap(~ outcome, ncol = 2, scales = "free_y") +
  theme_minimal(base_size = 12) +
  theme(
    panel.grid.minor = element_blank(),
    axis.text.y = element_text(hjust = 0),
    strip.text = element_text(face = "bold", size = 12),
    plot.margin = margin(10, 60, 10, 10)  # 给右侧 P 值留出空白
  )
# P for interaction
g <- g + geom_text(
  data = p_ann_pos,
  aes(x = x_max * 0.98, y = y, label = p_txt),
  inherit.aes = FALSE, hjust = 1, vjust = 1, size = 3.4
)
print(g)

##Table 3
if (!("real_food_cpi" %in% names(prices))) {
  val <- setdiff(names(prices), c("year","month","date"))[1]
  setnames(prices, val, "real_food_cpi")
}
prices <- prices %>% select(year, month, real_food_cpi) %>% distinct()
find_field_cols <- function(dat, field_id, instance = 2) {
  pat <- paste0("^f", field_id, "_", instance, "(_[0-9]+)?$")
  hit <- grep(pat, names(dat), value = TRUE)
  if (length(hit) == 0) {
    pat2 <- paste0("^f", field_id, "(_[2])?(_[0-9]+)?$") 
    hit <- grep(pat2, names(dat), value = TRUE)
  }
  hit
}
extract_ukb_value <- function(dat, field_ids, instance = 2) {
  for (fid in field_ids) {
    cols <- find_field_cols(dat, fid, instance = instance)
    if (length(cols) > 0) {
      mat <- as.matrix(sapply(dat[cols], function(x) suppressWarnings(as.numeric(x))))
      if (is.null(dim(mat))) return(mat)
      v <- apply(mat, 1, function(z) {
        z <- z[!is.na(z)]
        if (length(z) == 0) NA_real_ else z[1]
      })
      return(as.numeric(v))
    }
  }
  rep(NA_real_, nrow(dat))
}
# 2)  MRI 
field_ids <- list(
  LVEF   = c(22420),
  LVEDV  = c(22421, 24100, 31061),
  LVESV  = c(22422, 24101, 31062),
  LVSV   = c(22423, 31064),
  LVMASS = c(31063, 24105),
  BSA    = c(22427)
)
df <- df0
df$LVEF   <- extract_ukb_value(df, field_ids$LVEF,   instance = 2) # %
df$LVEDV  <- extract_ukb_value(df, field_ids$LVEDV,  instance = 2) # mL
df$LVESV  <- extract_ukb_value(df, field_ids$LVESV,  instance = 2) # mL
df$LVSV   <- extract_ukb_value(df, field_ids$LVSV,   instance = 2) # mL
df$LVMASS <- extract_ukb_value(df, field_ids$LVMASS, instance = 2) # g
df$BSA    <- extract_ukb_value(df, field_ids$BSA,    instance = 2) # m^2
df$LVSVI  <- ifelse(!is.na(df$BSA) & df$BSA > 0, df$LVSV  / df$BSA, NA)
df$LVEDVI <- ifelse(!is.na(df$BSA) & df$BSA > 0, df$LVEDV / df$BSA, NA)
df$LVMI   <- ifelse(!is.na(df$BSA) & df$BSA > 0, df$LVMASS/ df$BSA, NA)
df$LVMVR  <- ifelse(!is.na(df$LVEDV) & df$LVEDV > 0, df$LVMASS/ df$LVEDV, NA)

# （Rationed vs Not rationed）
stopifnot("birth_group" %in% names(df))
df$rationed2 <- ifelse(df$birth_group %in% 6:9, "Not rationed",
                       ifelse(df$birth_group %in% 1:5, "Rationed", NA))
df$rationed2 <- factor(df$rationed2, levels = c("Not rationed","Rationed"))
stopifnot(all(c("yob","mob") %in% names(df)))
df <- df %>%
  left_join(prices, by = c("yob" = "year", "mob" = "month"))
df <- df %>%
  group_by(yob) %>%
  mutate(real_food_cpi = ifelse(is.na(real_food_cpi),
                                mean(real_food_cpi, na.rm = TRUE),
                                real_food_cpi)) %>%
  ungroup()
if (any(is.na(df$real_food_cpi))) {
  df$real_food_cpi[is.na(df$real_food_cpi)] <- mean(df$real_food_cpi, na.rm = TRUE)
}
if (!("age" %in% names(df))) {
  if (!all(c("baseline_date") %in% names(df))) stop("需要 age 或 baseline_date")
  dob_mid <- as.Date(paste0(df$yob, "-", ifelse(is.na(df$mob), 6, df$mob), "-15"))
  df$age <- as.numeric(time_length(interval(dob_mid, as.Date(df$baseline_date)), "years"))
}
# sex/ethnicity/birth_place/birth_month/survey_year
if (!is.factor(df$sex))        df$sex        <- factor(df$sex)
if (!is.factor(df$ethnicity))  df$ethnicity  <- factor(df$ethnicity)
if (!is.factor(df$birth_place))df$birth_place<- factor(df$birth_place)
df$birth_month <- factor(df$mob, levels = 1:12)
if (!("survey_year" %in% names(df))) {
  dtcols <- grep("^f53_2(_[0-9]+)?$", names(df), value = TRUE)
  if (length(dtcols) > 0) {
    tmp <- suppressWarnings(as.Date(df[[dtcols[1]]]))
    df$survey_year <- year(tmp)
  } else {
    df$survey_year <- year(as.Date(df$baseline_date))
  }
}
bin_vars <- c("parent_cvd","parent_diab","parent_htn","maternal_smoke","breastfed")
for (v in bin_vars) {
  if (!(v %in% names(df))) stop(paste("缺少协变量:", v))
  df[[v]] <- as.integer(df[[v]])
}

# MRI 
any_cmr <- with(df, !is.na(LVSVI) | !is.na(LVMI) | !is.na(LVEDVI) | !is.na(LVMVR) | !is.na(LVEF))
dat <- df %>% filter(any_cmr, !is.na(rationed2))
nice_mean_sd_n <- function(x) {
  m <- mean(x, na.rm = TRUE); s <- sd(x, na.rm = TRUE); n <- sum(!is.na(x))
  sprintf("%.1f (%.1f)\n(n=%d)", m, s, n)
}
fit_lm_and_format <- function(dat, yvar, model = 1) {
  if (model == 1) {
    form <- as.formula(paste0(yvar, " ~ rationed2 + age + sex"))
  } else {
    form <- as.formula(paste0(
      yvar, " ~ rationed2 + age + sex + ethnicity + birth_place + birth_month + ",
      "real_food_cpi + parent_cvd + parent_diab + parent_htn + maternal_smoke + breastfed + survey_year"
    ))
  }
  fit <- lm(form, data = dat)
  sm  <- broom::tidy(fit, conf.int = TRUE)
  row <- sm %>% filter(term == "rationed2Rationed")
  if (nrow(row) == 0) return(list(txt = "NA", p = NA))
  txt <- sprintf("%.2f (%.2f to %.2f)", row$estimate, row$conf.low, row$conf.high)
  list(txt = txt, p = row$p.value)
}
indicators <- tribble(
  ~indicator, ~y,        ~unit,
  "LVSVI, mL/m^2",       "LVSVI",  "mL/m^2",
  "LVMI, g/m^2",         "LVMI",   "g/m^2",
  "LVEDVI, mL/m^2",      "LVEDVI", "mL/m^2",
  "LVMVR, g/mL",         "LVMVR",  "g/mL",
  "LVEF, %",             "LVEF",   "%"
)
make_one_row <- function(ind, ycol) {
  dsub <- dat %>% filter(!is.na(.data[[ycol]]))
  # mean±SD
  gsum <- dsub %>%
    group_by(rationed2) %>%
    summarise(val = nice_mean_sd_n(.data[[ycol]]), .groups = "drop") %>%
    tidyr::pivot_wider(names_from = rationed2, values_from = val)
  # 模型
  m1 <- fit_lm_and_format(dsub, ycol, model = 1)
  m2 <- fit_lm_and_format(dsub, ycol, model = 2)
  tibble(
    Indicator = ind,
    Rationed = gsum$`Rationed`,
    `Not rationed` = gsum$`Not rationed`,
    `Model 1 (coef, 95% CI)` = m1$txt,
    `P value 1` = ifelse(is.na(m1$p), "NA",
                         ifelse(m1$p < 0.001, "<0.001", sprintf("%.3f", m1$p))),
    `Model 2 (coef, 95% CI)` = m2$txt,
    `P value 2` = ifelse(is.na(m2$p), "NA",
                         ifelse(m2$p < 0.001, "<0.001", sprintf("%.3f", m2$p)))
  )
}
tbl_rows <- pmap(indicators, ~make_one_row(..1, ..2)) %>% bind_rows()

cap <- "UK Biobank imaging study"
gt_tbl <- gt(tbl_rows) %>%
  tab_header(title = md("Table 3 ")) %>%
  cols_align(align = "left", columns = c(Indicator)) %>%
  cols_align(align = "center", columns = c(Rationed, `Not rationed`,
                                           `Model 1 (coef, 95% CI)`, `P value 1`,
                                           `Model 2 (coef, 95% CI)`, `P value 2`)) %>%
  tab_source_note(md("Model 1. Model 2")) %>%
  opt_table_lines()

print(gt_tbl)

###############################HRS
# HRS external control cohort: cleaning, exclusions, and frequency matching
design <- c(
  # birth year/month (RAND)
  "rabyear_randhrs1992_2020v2",
  "rabmonth_randhrs1992_2020v2",
  # adoption (respondent was adopted as a child; RAND top-level flag)
  "raadopt_randhrs1992_2020v2",
  # age at interview (baseline; wave 4 for our panel)
  "r4agey_b_randhrs1992_2020v2",
  # sex, race
  "ragender_randhrs1992_2020v2",
  "raracem_randhrs1992_2020v2",
  # education, marital status, vigorous physical activity, total wealth
  "raeduc_randhrs1992_2020v2",
  "r4mstat_randhrs1992_2020v2",
  "r4vigact_randhrs1992_2020v2",
  "h4atotb_randhrs1992_2020v2",
  # smoking, drinking
  "r4smokev_randhrs1992_2020v2",
  "r4drink_randhrs1992_2020v2",
  # self-reported hypertension/diabetes at wave4
  "r4hibpe_randhrs1992_2020v2",
  "r4diabe_randhrs1992_2020v2",
  # heart problems across waves 4–12 (HRS-harmonized 0/1)
  "r4heart_randhrs1992_2020v2", "r5heart_randhrs1992_2020v2", "r6heart_randhrs1992_2020v2",
  "r7heart_randhrs1992_2020v2", "r8heart_randhrs1992_2020v2", "r9heart_randhrs1992_2020v2",
  "r10heart_randhrs1992_2020v2", "r11heart_randhrs1992_2020v2", "r12heart_randhrs1992_2020v2",
  # household-person ID (unique key)
  "rahhidpn_randhrs1992_2020v2"
)
column_names <- get_descriptions(design)
raw_df <- fetch_HRS_data(design, join = "left", colnames = column_names)
setDT(raw_df)

# 1) Standardize column names
std_names <- function(x) {
  nm <- ifelse(grepl(":", x), sub(":.*$", "", x), x)
  nm <- sub("_randhrs1992_2020v2$", "", nm, ignore.case = TRUE)
  nm
}
setnames(raw_df, old = names(raw_df), new = std_names(names(raw_df)))
# S keep only first occurrence if duplicated
if (any(duplicated(names(raw_df)))) {
  raw_df <- raw_df[, !duplicated(names(raw_df)), with = FALSE]
}
# 2) Build a clean analysis frame (HRS)
recode_binary <- function(x, one = 1, zero = 0, labels = c("No","Yes")) {
  y <- ifelse(is.na(x), NA_integer_,
              ifelse(x == one, 1L, ifelse(x == zero, 0L, NA_integer_)))
  factor(ifelse(is.na(y), NA, ifelse(y == 1L, labels[2], labels[1])),
         levels = labels)
}
# Identify heart columns for waves 4–12
heart_vars <- paste0("r", 4:12, "heart")
have_heart_cols <- heart_vars[heart_vars %in% names(raw_df)]
stopifnot(length(have_heart_cols) > 0)
# Unique respondent ID
stopifnot("rahhidpn" %in% names(raw_df))
# Clean up
HRS <- raw_df %>%
  transmute(
    ID        = rahhidpn,
    birth_y   = as.integer(rabyear),
    birth_m   = as.integer(rabmonth),
    adopted   = if ("raadopt" %in% names(raw_df)) as.integer(raadopt) else NA_integer_,
    age_w4    = as.numeric(r4agey_b),
    sex       = factor(ifelse(ragender == 1, "Male",
                              ifelse(ragender == 2, "Female", NA)), levels = c("Male","Female")),
    race3     = factor(case_when(
      raracem == 1 ~ "White",
      raracem == 2 ~ "Black",
      raracem == 3 ~ "Other",
      TRUE ~ NA_character_
    ), levels = c("White","Black","Other")),
    race2     = factor(case_when(
      raracem == 1 ~ "White",
      raracem %in% c(2,3) ~ "Non-white",
      TRUE ~ NA_character_
    ), levels = c("White","Non-white")),
    educ_cat  = case_when(
      raeduc %in% c(1) ~ "Below high school",
      raeduc %in% c(2,3) ~ "High school",
      raeduc %in% c(4,5) ~ "College or above",
      TRUE ~ NA_character_
    ),
    marital   = case_when(
      r4mstat %in% c(1,2,3) ~ "Married/partnered",
      r4mstat %in% c(4,5,6,7) ~ "Separated/Divorced/Widowed",
      r4mstat == 8 ~ "Never married",
      TRUE ~ NA_character_
    ),
    vigact    = case_when(
      r4vigact == 1 ~ "Vigorous ≥3/wk",
      r4vigact %in% c(0,2) ~ "Vigorous <3/wk",
      TRUE ~ NA_character_
    ),
    wealth    = suppressWarnings(as.numeric(h4atotb)),
    smoke_ev  = recode_binary(r4smokev, one = 1, zero = 0, labels = c("Never","Ever")),
    drink_ev  = recode_binary(r4drink,  one = 1, zero = 0, labels = c("Never","Ever")),
    htn_ev    = recode_binary(r4hibpe,  one = 1, zero = 0),
    dm_ev     = recode_binary(r4diabe,  one = 1, zero = 0)
  )
# Add heart status/time using the raw 0/1 waves
# Prevalent at baseline (wave 4):
HRS$heart_w4 <- raw_df$r4heart
HRS$heart_any <- apply(as.data.frame(raw_df[, ..have_heart_cols]), 1, function(z) any(z == 1, na.rm = TRUE))
# Time to first heart problem in years since wave 4 (waves are biennial)
first_wave_index <- apply(as.data.frame(raw_df[, ..have_heart_cols]), 1, function(z) {
  i <- which(z == 1)
  if (length(i) == 0) return(NA_integer_) else return(i[1])
})
# wave index 1 
HRS$heart_time_years <- ifelse(is.na(first_wave_index), NA_real_, (first_wave_index - 1) * 2)
# 3) Define rationing exposure using birth year & month
# -----------------------------
in_window <- with(HRS, (birth_y > 1951 & birth_y < 1956) |
                    (birth_y == 1951 & birth_m >= 10) |
                    (birth_y == 1956 & birth_m <= 3))

HRS$focus_period <- ifelse(in_window, 1L, 0L)

HRS$Sugar_ration <- with(HRS, case_when(
  (birth_y == 1951 & birth_m >= 10) | (birth_y == 1952) | (birth_y == 1953) ~ "Rationed",
  (birth_y == 1955) | (birth_y == 1956 & birth_m <= 3) ~ "Not rationed",
  TRUE ~ NA_character_
))
HRS$Sugar_ration <- factor(HRS$Sugar_ration, levels = c("Rationed","Not rationed"))
# 4) Build exclusion flags exactly as in the flow
# Initial base: all participants (we will count later)
N_initial <- nrow(HRS)
hrs_focus <- HRS %>% filter(focus_period == 1)
N_focus_all <- nrow(hrs_focus)
hrs_no_prev <- hrs_focus %>% filter(is.na(heart_w4) | heart_w4 == 0)
N_prev_excluded <- N_focus_all - nrow(hrs_no_prev)
covars_required <- c("sex","race2","age_w4","educ_cat","marital","vigact","wealth",
                     "smoke_ev","drink_ev","htn_ev","dm_ev","Sugar_ration")
hrs_no_prev$na_cov <- apply(hrs_no_prev[, covars_required], 1, function(row) any(is.na(row)))
hrs_covOK <- hrs_no_prev %>% filter(!na_cov)
N_cov_missing <- nrow(hrs_no_prev) - nrow(hrs_covOK)
hrs_covOK$adopted_flag <- ifelse(is.na(hrs_covOK$adopted), 0L, ifelse(hrs_covOK$adopted == 1L, 1L, 0L))
hrs_final_pool <- hrs_covOK %>% filter(adopted_flag == 0)
N_adopted_excluded <- nrow(hrs_covOK) - nrow(hrs_final_pool)
# 5) Frequency matching with main cohort by sex and race
  main_dist <- tribble(
    ~sex,    ~race2,       ~target_n,
    "Male",  "White",      0,
    "Male",  "Non-white",  0,
    "Female","White",      0,
    "Female","Non-white",  0
  )
  balanced_sample <- function(df, strata_vars, N_total) {
    tab <- df %>% count(across(all_of(strata_vars)), name = "avail")
    k <- nrow(tab)
    base_n <- floor(N_total / k)
    tab$take <- pmin(tab$avail, base_n)
    # distribute remaining
    rem <- N_total - sum(tab$take)
    if (rem > 0) {
      ord <- order(-tab$avail)
      i <- 1
      while (rem > 0 && i <= k) {
        idx <- ord[i]
        if (tab$take[idx] < tab$avail[idx]) {
          tab$take[idx] <- tab$take[idx] + 1
          rem <- rem - 1
        }
        i <- i + 1
        if (i > k) i <- 1
      }
    }
    # sample within each stratum
    out <- list()
    for (ii in seq_len(k)) {
      ss <- tab[ii, ]
      dss <- df %>% filter(across(all_of(strata_vars), ~ .x == ss[[.col]]))
      n_take <- ss$take
      if (n_take > 0) {
        out[[ii]] <- dss %>% slice_sample(n = n_take)
      }
    }
    bind_rows(out)
  }
# Perform matching
if (exists("main_dist") && is.data.frame(main_dist)) {
  pool <- hrs_final_pool
  take_list <- list()
  rem <- 0
  for (i in 1:nrow(main_dist)) {
    sx <- main_dist$sex[i]; rc <- main_dist$race2[i]; t_n <- main_dist$target_n[i]
    dss <- pool %>% filter(sex == sx, race2 == rc)
    n_take <- min(nrow(dss), t_n)
    take_list[[length(take_list)+1]] <- dss %>% slice_sample(n = n_take)
    pool <- anti_join(pool, take_list[[length(take_list)]], by = "ID")
    if (nrow(dss) < t_n) rem <- rem + (t_n - nrow(dss))
  }
  # allocate leftover
  if (rem > 0 && nrow(pool) > 0) {
    extra <- pool %>% slice_sample(n = min(rem, nrow(pool)))
    take_list[[length(take_list)+1]] <- extra
  }
  hrs_matched <- bind_rows(take_list)
} else {
  hrs_matched <- balanced_sample(hrs_final_pool, c("sex","race2"), N_target)
}
# 6) Split by exposure (Rationed vs Not rationed)
hrs_matched <- hrs_matched %>%
  filter(!is.na(Sugar_ration)) %>%
  mutate(group_simple = factor(Sugar_ration, levels = c("Rationed","Not rationed")))
HRS_analysis <- hrs_matched %>%
  select(ID, birth_y, birth_m, sex, race2, race3, age_w4, educ_cat, marital, vigact, wealth,
         smoke_ev, drink_ev, htn_ev, dm_ev, Sugar_ration,
         heart_w4, heart_any, heart_time_years)
HRS_analysis <- as.data.frame(HRS_analysis)

# ELSA external validation cohort
design2 <- c(
  # Place of birth / birth year / birth month / adoption
  "rabplace_h_elsa_g3",     # 1 UK; 11 elsewhere outside UK
  "rabyear_h_elsa_g3",      # birth year
  "rabmonth_h_elsa_g3",     # birth month (added)
  "raadopt_h_elsa_g3",      # adopted (added; 1 yes)
  
  # Baseline age (wave 1), sex, race
  "r1agey_h_elsa_g3",
  "ragender_h_elsa_g3",     # 1 Man; 2 Woman
  "raracem_h_elsa_g3",      # 1 White; 4 Non-white
  
  # Lifestyle / SES / health history
  "r1vgactx_e_h_elsa_g3",   # 2 >1/week; 3 1/week; 4 1-3/month; 5 never
  "raeduc_e_h_elsa_g3",     # 1 <HS; 3 HS; 4/5 College+
  "r1mstat_h_elsa_g3",      # marital status
  "h1atotb_h_elsa_g3",      # total family wealth
  "r1smokev_h_elsa_g3",     # smoke ever (0 No; 1 Yes)
  "r1drink_h_elsa_g3",      # drink ever (0 No; 1 Yes)
  "r1hibpe_h_elsa_g3",      # ever HTN (0/1)
  "r1diabe_h_elsa_g3",      # ever DM (0/1)
  
  # Heart problems across waves 1-9
  "r1hearte_h_elsa_g3","r2hearte_h_elsa_g3","r3hearte_h_elsa_g3",
  "r4hearte_h_elsa_g3","r5hearte_h_elsa_g3","r6hearte_h_elsa_g3",
  "r7hearte_h_elsa_g3","r8hearte_h_elsa_g3","r9hearte_h_elsa_g3",
  
  # Stroke (1-9) — not strictly needed for this flow, but left here for extension
  "r1stroke_h_elsa_g3","r2stroke_h_elsa_g3","r3stroke_h_elsa_g3",
  "r4stroke_h_elsa_g3","r5stroke_h_elsa_g3","r6stroke_h_elsa_g3",
  "r7stroke_h_elsa_g3","r8stroke_h_elsa_g3","r9stroke_h_elsa_g3",
  
  # CHF (1-9) — not used in flow, but handy to keep consistent with HRS style
  "r1conhrtfe_h_elsa_g3","r2conhrtfe_h_elsa_g3","r3conhrtfe_h_elsa_g3",
  "r4conhrtfe_h_elsa_g3","r5conhrtfe_h_elsa_g3","r6conhrtfe_h_elsa_g3",
  "r7conhrtfe_h_elsa_g3","r8conhrtfe_h_elsa_g3","r9conhrtfe_h_elsa_g3",
  
  # Unique ID
  "idauniq_h_elsa_g3"
)
column_names2 <- get_descriptions(design2)
raw2 <- fetch_ELSA_data(design2, 'left', column_names2)
setDT(raw2)
std_names <- function(x) {
  nm <- ifelse(grepl(":", x), sub(":.*$", "", x), x)
  nm <- sub("_h_elsa_g3$", "", nm, ignore.case = TRUE)
  nm
}
setnames(raw2, old = names(raw2), new = std_names(names(raw2)))
if (any(duplicated(names(raw2)))) raw2 <- raw2[, !duplicated(names(raw2)), with = FALSE]
# 2) Build clean variables
#  recode binary (0/1) to factor with "No/Yes"
recode01 <- function(x, lbl = c("No","Yes")) {
  y <- ifelse(is.na(x), NA_integer_,
              ifelse(x == 1, 1L, ifelse(x == 0, 0L, NA_integer_)))
  factor(ifelse(is.na(y), NA, ifelse(y == 1L, lbl[2], lbl[1])), levels = lbl)
}
# Heart variables present?
heart_vars <- paste0("r", 1:9, "hearte")
heart_vars <- heart_vars[heart_vars %in% names(raw2)]
stopifnot(length(heart_vars) > 0)
ELSA <- raw2 %>%
  transmute(
    ID          = idauniq,
    birth_y     = as.integer(rabyear),
    birth_m     = as.integer(rabmonth),
    birth_place = as.integer(rabplace),  # 1 UK; 11 elsewhere
    adopted     = if ("raadopt" %in% names(raw2)) as.integer(raadopt) else NA_integer_,
    
    age_w1      = suppressWarnings(as.numeric(r1agey)),
    sex         = factor(ifelse(ragender == 1, "Male",
                                ifelse(ragender == 2, "Female", NA)),
                         levels = c("Male","Female")),
    race2       = factor(ifelse(raracem == 1, "White",
                                ifelse(raracem == 4, "Non-white", NA)),
                         levels = c("White","Non-white")),
    educ_cat    = case_when(
      raeduc_e == 1 ~ "Below high school",
      raeduc_e == 3 ~ "High school",
      raeduc_e %in% c(4,5) ~ "College or above",
      TRUE ~ NA_character_
    ),
    marital     = case_when(
      r1mstat %in% c(1,2) ~ "Married/partnered",
      r1mstat %in% c(4,5,7) ~ "Separated/Divorced/Widowed",
      r1mstat == 8 ~ "Never married",
      TRUE ~ NA_character_
    ),
    vigact      = case_when(
      r1vgactx_e == 2 ~ ">1/week",
      r1vgactx_e == 3 ~ "1/week",
      r1vgactx_e == 4 ~ "1-3/month",
      r1vgactx_e == 5 ~ "Hardly ever/never",
      TRUE ~ NA_character_
    ),
    wealth      = suppressWarnings(as.numeric(h1atotb)),
    smoke_ev    = recode01(r1smokev, c("Never","Ever")),
    drink_ev    = recode01(r1drink,  c("Never","Ever")),
    htn_ev      = recode01(r1hibpe),
    dm_ev       = recode01(r1diabe),
    # baseline prevalent heart problem (wave 1)
    heart_w1    = as.integer(r1hearte)
  )
# Any heart problem during waves 1-9
ELSA$heart_any <- apply(as.data.frame(raw2[, ..heart_vars]), 1, function(z) any(z == 1, na.rm = TRUE))
# Time to first heart problem from wave 1 (0,2,...,16 years)
first_wave_idx <- apply(as.data.frame(raw2[, ..heart_vars]), 1, function(z) {
  i <- which(z == 1)
  if (length(i) == 0) NA_integer_ else i[1]
})
ELSA$heart_time_years <- ifelse(is.na(first_wave_idx), NA_real_, (first_wave_idx - 1) * 2)
# 3) Define focusing period & rationing exposure
in_window <- with(ELSA, (birth_y > 1951 & birth_y < 1956) |
                    (birth_y == 1951 & birth_m >= 10) |
                    (birth_y == 1956 & birth_m <= 3))
ELSA$focus_period <- ifelse(in_window, 1L, 0L)
ELSA$Sugar_ration <- with(ELSA, case_when(
  (birth_y == 1951 & birth_m >= 10) | (birth_y == 1952) | (birth_y == 1953) ~ "Rationed",
  (birth_y == 1955) | (birth_y == 1956 & birth_m <= 3) ~ "Not rationed",
  TRUE ~ NA_character_
))
ELSA$Sugar_ration <- factor(ELSA$Sugar_ration, levels = c("Rationed","Not rationed"))
# 4) Exclusions according to the flow
N_initial <- nrow(ELSA)   
# A) period births
elsa_focus <- ELSA %>% filter(focus_period == 1)
N_focus_all <- nrow(elsa_focus)  # 
# B) Exclude born outside UK
elsa_focus$born_uk <- ifelse(elsa_focus$birth_place == 1, 1L,
                             ifelse(is.na(elsa_focus$birth_place), NA_integer_, 0L))
elsa_in_uk <- elsa_focus %>% filter(born_uk == 1L | is.na(born_uk))  # if unknown, keep (conservative)
N_born_outside_excl <- nrow(elsa_focus) - nrow(elsa_in_uk)
# C) Exclude adopted 
elsa_in_uk$adopted_flag <- ifelse(is.na(elsa_in_uk$adopted), 0L,
                                  ifelse(elsa_in_uk$adopted == 1L, 1L, 0L))
elsa_not_adopted <- elsa_in_uk %>% filter(adopted_flag == 0L)
N_adopted_excl <- nrow(elsa_in_uk) - nrow(elsa_not_adopted)
# D) Exclude prevalent heart problem at baseline
elsa_no_prev <- elsa_not_adopted %>% filter(is.na(heart_w1) | heart_w1 == 0L)
N_prev_excl <- nrow(elsa_not_adopted) - nrow(elsa_no_prev)
# E) Exclude missing covariates 
covars_required <- c("sex","race2","age_w1","educ_cat","marital","vigact",
                     "wealth","smoke_ev","drink_ev","htn_ev","dm_ev","Sugar_ration")
elsa_no_prev$na_cov <- apply(elsa_no_prev[, covars_required], 1, function(r) any(is.na(r)))
elsa_covOK <- elsa_no_prev %>% filter(!na_cov)
N_covmiss_excl <- nrow(elsa_no_prev) - nrow(elsa_covOK)
#  matching
pool <- elsa_covOK
# 5) Frequency matching by sex & race
balanced_sample <- function(df, strata_vars, N_total) {
  tab <- df %>% count(across(all_of(strata_vars)), name = "avail")
  k <- nrow(tab)
  base_n <- floor(N_total / k)
  tab$take <- pmin(tab$avail, base_n)
  rem <- N_total - sum(tab$take)
  if (rem > 0) {
    ord <- order(-tab$avail)
    i <- 1
    while (rem > 0 && any(tab$take < tab$avail)) {
      idx <- ord[i]
      if (tab$take[idx] < tab$avail[idx]) {
        tab$take[idx] <- tab$take[idx] + 1
        rem <- rem - 1
      }
      i <- ifelse(i == k, 1, i + 1)
    }
  }
  out <- list()
  for (ii in 1:nrow(tab)) {
    ss <- tab[ii, ]
    dss <- df %>% filter(across(all_of(strata_vars), ~ .x == ss[[.col]]))
    if (ss$take > 0) {
    }
  }
  bind_rows(out)
}
if (exists("main_dist") && is.data.frame(main_dist)) {
  pool2 <- pool
  takes <- list(); rem <- 0
  for (i in 1:nrow(main_dist)) {
    sx <- main_dist$sex[i]; rc <- main_dist$race2[i]; tn <- main_dist$target_n[i]
    sub <- pool2 %>% filter(sex == sx, race2 == rc)
    take_n <- min(nrow(sub), tn)
    if (take_n > 0) takes[[length(takes)+1]] <- sub %>% slice_sample(n = take_n)
    pool2 <- anti_join(pool2, bind_rows(takes), by = "ID")
    if (nrow(sub) < tn) rem <- rem + (tn - nrow(sub))
  }
  if (rem > 0 && nrow(pool2) > 0)
    takes[[length(takes)+1]] <- pool2 %>% slice_sample(n = min(rem, nrow(pool2)))
  elsa_matched <- bind_rows(takes)
} else {
  elsa_matched <- balanced_sample(pool, c("sex","race2"), N_target)
}
tab_expo <- elsa_matched %>%
  filter(!is.na(Sugar_ration)) %>%
  count(Sugar_ration, name = "n")
ELSA_analysis <- elsa_matched %>%
  select(ID, birth_y, birth_m, birth_place, age_w1, sex, race2, educ_cat, marital,
         vigact, wealth, smoke_ev, drink_ev, htn_ev, dm_ev,
         Sugar_ration, heart_w1, heart_any, heart_time_years)
################Analysis
ELSA_df <- ELSA_analysis %>%
  mutate(
    cohort = "ELSA",
    age = coalesce(.data$age_w1, .data$age),    
    survey_year = if ("survey_year" %in% names(.)) survey_year else 2002
  )
HRS_df <- HRS_analysis %>%
  mutate(
    cohort = "HRS",
    age = coalesce(.data$age_w4, .data$age),
    survey_year = if ("survey_year" %in% names(.)) survey_year else 1998
  )
# Keep the essentials and standardize variable names
keep_vars <- c("ID","cohort","age","sex","race2","educ_cat","marital",
               "Sugar_ration","heart_time_years","heart_any","survey_year")
ELSA_df <- ELSA_df %>% select(any_of(keep_vars))
HRS_df  <- HRS_df  %>% select(any_of(keep_vars))
# Ensure group factor order and encode time/event
prep_surv <- function(dat) {
  dat %>%
    filter(!is.na(Sugar_ration), Sugar_ration %in% c("Rationed","Not rationed")) %>%
    mutate(
      Sugar_ration = factor(Sugar_ration, levels = c("Rationed","Not rationed")),
      # event time: first heart problem (0..16) or censor at 18 years
      time = ifelse(is.na(heart_time_years), 18, pmin(heart_time_years, 18)),
      event = ifelse(is.na(heart_time_years), 0, 1)
    ) %>%
    # basic sanity
    filter(is.finite(time), time >= 0, time <= 18)
}
ELSA_df <- prep_surv(ELSA_df)
HRS_df  <- prep_surv(HRS_df)
# 1) Plot
plot_ci <- function(dat, title_lab, palette = c("#E64B35", "#00A087")) {
  fit <- survfit(Surv(time, event) ~ Sugar_ration, data = dat)
  g <- ggsurvplot(
    fit,
    data = dat,
    fun = "event",
    risk.table = TRUE,
    risk.table.y.text.col = TRUE,
    risk.table.height = 0.28,
    break.time.by = 3, xlim = c(0, 18),
    xlab = "Follow-up Time (years)",
    ylab = "Cumulative incidence",
    legend.title = "",
    legend.labs = c("Rationed", "Non-rationed"),
    palette = palette,
    pval = TRUE, pval.coord = c(9, 0.02),  # show logrank p near bottom right
    conf.int = TRUE, censor = FALSE
  )
  g$plot <- g$plot +
    ggtitle(title_lab) +
    theme_minimal(base_size = 12) +
    theme(legend.position = "top",
          plot.title = element_text(face = "bold", hjust = 0, size = 12))
  g
}
g_el <- plot_ci(ELSA_df, "(A) ELSA")
g_hr <- plot_ci(HRS_df,  "(B) HRS")
p_combined <- arrange_ggsurvplots(list(g_el, g_hr), print = FALSE, ncol = 2)
print(p_combined)
# Person-years and events by group
summarise_py <- function(dat) {
  dat %>%
    group_by(Sugar_ration) %>%
    summarise(
      events = sum(event == 1, na.rm = TRUE),
      person_years = sum(time, na.rm = TRUE),
      N = n(), .groups = "drop"
    )
}
# Format "Event (n)/Person-years (N)"
fmt_epy <- function(e, py, n) {
  sprintf("%d/%.0f (%d)", e, py, n)
}
# Fit Gompertz models
hr_gompertz <- function(dat, model = 1) {
  vars_m1 <- c("Sugar_ration","age","sex","race2","time","event")
  vars_m2 <- c(vars_m1, "educ_cat","marital")
  vars_m3 <- c(vars_m2, "survey_year")
  use <- switch(as.character(model),
                "1" = vars_m1,
                "2" = vars_m2,
                "3" = vars_m3)
  d <- dat %>% select(all_of(use)) %>% na.omit()
  rhs <- switch(as.character(model),
                "1" = "Sugar_ration + age + sex + race2",
                "2" = "Sugar_ration + age + sex + race2 + educ_cat + marital",
                "3" = "Sugar_ration + age + sex + race2 + educ_cat + marital + survey_year")
  form <- as.formula(paste0("Surv(time, event) ~ ", rhs))
  # Fit Gompertz
  fit <- flexsurvreg(form, data = d, dist = "gompertz")
  sm  <- broom::tidy(fit)
  row <- sm %>% filter(term == "rate_Sugar_rationRationed")
  hr  <- exp(row$estimate)
  lcl <- exp(row$estimate - 1.96 * row$std.error)
  ucl <- exp(row$estimate + 1.96 * row$std.error)
  p   <- 2 * pnorm(-abs(row$estimate / row$std.error))
  list(hr = hr, lcl = lcl, ucl = ucl, p = p)
}
fmt_hr <- function(hr, l, u) sprintf("%.2f (%.2f–%.2f)", hr, l, u)
fmt_p  <- function(p) ifelse(is.na(p), "NA", ifelse(p < 0.001, "<0.001", sprintf("%.3f", p)))
make_block <- function(dat, cohort_name) {
  # events/person-years
  ep <- summarise_py(dat)
  e_nr  <- ep$events[ep$Sugar_ration == "Not rationed"]
  py_nr <- ep$person_years[ep$Sugar_ration == "Not rationed"]
  n_nr  <- ep$N[ep$Sugar_ration == "Not rationed"]
  e_ra  <- ep$events[ep$Sugar_ration == "Rationed"]
  py_ra <- ep$person_years[ep$Sugar_ration == "Rationed"]
  n_ra  <- ep$N[ep$Sugar_ration == "Rationed"]
  m1 <- hr_gompertz(dat, 1); m2 <- hr_gompertz(dat, 2); m3 <- hr_gompertz(dat, 3)
  tibble::tibble(
    Cohort = cohort_name,
    `Event (n)/Person-years in non-rationed participants (N)` = fmt_epy(e_nr, py_nr, n_nr),
    `Event (n)/Person-years in rationed participants (N)`     = fmt_epy(e_ra, py_ra, n_ra),
    `Rationed vs not rationed—Model 1 HR (95% CI)` = fmt_hr(m1$hr, m1$lcl, m1$ucl),
    `P for model 1` = fmt_p(m1$p),
    `Rationed vs not rationed—Model 2 HR (95% CI)` = fmt_hr(m2$hr, m2$lcl, m2$ucl),
    `P for model 2` = fmt_p(m2$p),
    `Rationed vs not rationed—Model 3 HR (95% CI)` = fmt_hr(m3$hr, m3$lcl, m3$ucl),
    `P for model 3` = fmt_p(m3$p)
  )
}
tbl_C <- bind_rows(
  make_block(ELSA_df, "ELSA"),
  make_block(HRS_df,  "HRS")
)
#Standard mediation analysis 
if (!("sugar_ration" %in% names(dat0))) {
  if ("rationed2" %in% names(dat0)) {
    dat0$sugar_ration <- ifelse(dat0$rationed2 == "Rationed", 1L,
                                ifelse(dat0$rationed2 == "Not rationed", 0L, NA_integer_))
  } else if ("birth_group" %in% names(dat0)) {
    dat0$sugar_ration <- ifelse(dat0$birth_group %in% 1:5, 1L,
                                ifelse(dat0$birth_group %in% 6:9, 0L, NA_integer_))
  } else {
    stop("Provide either `rationed2` or `birth_group` to construct sugar_ration.")
  }
}
# Mediators
req_med <- c("ev_t2dm","ev_htn","birth_weight_kg")
miss_med <- setdiff(req_med, names(dat0))
if (length(miss_med) > 0) {
  stop(paste("Missing mediator columns:", paste(miss_med, collapse = ", ")))
}
# Covariates (Model 2 set)
covars <- c("age","sex","eth2","birth_place","birth_month","real_food_cpi",
            "parent_cvd","parent_diab","parent_htn","maternal_smoke","breastfed",
            "survey_year","GRS_CVD")  # GRS optional
covars <- covars[covars %in% names(dat0)]  # keep available only
# Keep analysis rows
dat <- dat0 %>%
  select(any_of(c("sugar_ration","ev_cvd","ev_t2dm","ev_htn","birth_weight_kg", covars))) %>%
  mutate(across(c(sugar_ration, ev_cvd, ev_t2dm, ev_htn), ~ as.integer(.))) %>%
  filter(!is.na(sugar_ration), !is.na(ev_cvd))
#  linear models
if ("sex" %in% names(dat) && !is.factor(dat$sex)) dat$sex <- factor(dat$sex)
if ("eth2" %in% names(dat) && !is.factor(dat$eth2)) dat$eth2 <- factor(dat$eth2)
if ("birth_place"  %in% names(dat) && !is.factor(dat$birth_place)) dat$birth_place <- factor(dat$birth_place)
if ("birth_month"  %in% names(dat) && !is.factor(dat$birth_month)) dat$birth_month <- factor(dat$birth_month)
#    - ACME = a*b ; ADE = c' ; Total = a*b + c'
fit_lm <- function(fml, data) {
  lm(fml, data = data)
}
coef_p <- function(fit, term) {
  sm <- summary(fit)$coefficients
  if (!(term %in% rownames(sm))) return(c(NA, NA))
  c(beta = unname(sm[term, "Estimate"]),
    pval = unname(sm[term, "Pr(>|t|)"]))
}
fmt_bp <- function(beta, p) {
  paste0("\u03b2 = ", sprintf("%.2f", beta), "\nP ",
         ifelse(is.na(p), "= NA",
                ifelse(p < 0.001, "< 0.001", paste0("= ", sprintf("%.3f", p)))))
}
fmt_box <- function(acme, ade, te) {
  pm <- ifelse(is.na(te) || te == 0, NA_real_, acme/te)
  paste0("ACME = ", sprintf("%.2f", acme), "\n",
         "ADE = ", sprintf("%.2f", ade), "\n",
         "Total effect = ", sprintf("%.2f", te), "\n",
         "Prop. Mediated = ",
         ifelse(is.na(pm), "NA", paste0(sprintf("%.1f", 100*pm), "%")))
}
# single mediator
med_single <- function(data, med) {
  # total effect: Y ~ X + C
  f_total <- as.formula(paste("ev_cvd ~ sugar_ration +", paste(covars, collapse = " + ")))
  fit_total <- fit_lm(f_total, data)
  c_total   <- coef_p(fit_total, "sugar_ration")
  # a path: M ~ X + C
  f_a <- as.formula(paste(med, "~ sugar_ration +", paste(covars, collapse = " + ")))
  fit_a <- fit_lm(f_a, data)
  a <- coef_p(fit_a, "sugar_ration")
  # b & c' paths: Y ~ X + M + C
  f_b <- as.formula(paste("ev_cvd ~ sugar_ration +", med, "+", paste(covars, collapse = " + ")))
  fit_b <- fit_lm(f_b, data)
  b     <- coef_p(fit_b, med)
  cprime <- coef_p(fit_b, "sugar_ration")
  # effects
  acme <- a["beta"] * b["beta"]
  ade  <- cprime["beta"]
  te   <- acme + ade
  list(
    total = list(beta = c_total["beta"], p = c_total["pval"]),
    a     = list(beta = a["beta"],       p = a["pval"]),
    b     = list(beta = b["beta"],       p = b["pval"]),
    cprime= list(beta = cprime["beta"],  p = cprime["pval"]),
    effects = list(acme = acme, ade = ade, te = te)
  )
}
# Two mediators jointly (product-of-coefficients, additivity)
med_double <- function(data, m1, m2) {
  # totals
  f_total <- as.formula(paste("ev_cvd ~ sugar_ration +", paste(covars, collapse = " + ")))
  fit_total <- fit_lm(f_total, data)
  c_total   <- coef_p(fit_total, "sugar_ration")
  # a paths
  f_a1 <- as.formula(paste(m1, "~ sugar_ration +", paste(covars, collapse = " + ")))
  f_a2 <- as.formula(paste(m2, "~ sugar_ration +", paste(covars, collapse = " + ")))
  fit_a1 <- fit_lm(f_a1, data)
  fit_a2 <- fit_lm(f_a2, data)
  a1 <- coef_p(fit_a1, "sugar_ration")
  a2 <- coef_p(fit_a2, "sugar_ration")
  # b & c' : Y ~ X + M1 + M2 + C
  f_b <- as.formula(paste("ev_cvd ~ sugar_ration +", m1, "+", m2, "+", paste(covars, collapse = " + ")))
  fit_b <- fit_lm(f_b, data)
  b1 <- coef_p(fit_b, m1)
  b2 <- coef_p(fit_b, m2)
  cprime <- coef_p(fit_b, "sugar_ration")
  acme <- a1["beta"]*b1["beta"] + a2["beta"]*b2["beta"]
  ade  <- cprime["beta"]
  te   <- acme + ade
  list(
    total  = list(beta = c_total["beta"], p = c_total["pval"]),
    a1     = list(beta = a1["beta"], p = a1["pval"]),
    a2     = list(beta = a2["beta"], p = a2["pval"]),
    b1     = list(beta = b1["beta"], p = b1["pval"]),
    b2     = list(beta = b2["beta"], p = b2["pval"]),
    cprime = list(beta = cprime["beta"], p = cprime["pval"]),
    effects = list(acme = acme, ade = ade, te = te)
  )
}
# -----------------------------
# 2) Run mediation pieces
# -----------------------------
# (A) Total effect only
res_A <- med_single(dat, med = "ev_t2dm")  #  TE path
TE_only <- list(beta = res_A$total$beta, p = res_A$total$p)
# (B) T2DM mediator
res_B <- med_single(dat, med = "ev_t2dm")
# (C) Hypertension mediator
res_C <- med_single(dat, med = "ev_htn")
# (D) T2DM + Hypertension (joint mediation)
res_D <- med_double(dat, m1 = "ev_t2dm", m2 = "ev_htn")
# (E) Birth weight mediator (continuous)
res_E <- med_single(dat %>% filter(!is.na(birth_weight_kg)),
                    med = "birth_weight_kg")
# 3) Diagram 
final_plot <- gA + gB + gC + gD + gE + plot_layout(design = layout)
print(final_plot)
sum_tbl <- tibble::tribble(
  ~Panel, ~Mediator, ~ACME, ~ADE, ~Total_Effect, ~Prop_Mediated,
  "A",  "None",                       NA,                        NA,              TE_only$beta, NA,
  "B",  "Type 2 diabetes",            res_B$effects$acme,        res_B$effects$ade, res_B$effects$te,
  ifelse(res_B$effects$te==0, NA, res_B$effects$acme/res_B$effects$te),
  "C",  "Hypertension",               res_C$effects$acme,        res_C$effects$ade, res_C$effects$te,
  ifelse(res_C$effects$te==0, NA, res_C$effects$acme/res_C$effects$te),
  "D",  "T2DM + Hypertension",        res_D$effects$acme,        res_D$effects$ade, res_D$effects$te,
  ifelse(res_D$effects$te==0, NA, res_D$effects$acme/res_D$effects$te),
  "E",  "Birth weight (kg)",          res_E$effects$acme,        res_E$effects$ade, res_E$effects$te,
  ifelse(res_E$effects$te==0, NA, res_E$effects$acme/res_E$effects$te)
) %>%
  mutate(across(c(ACME, ADE, Total_Effect, Prop_Mediated),
                ~ ifelse(is.na(.), NA, round(., 3))))

# The scripts above implement an end-to-end pipeline for data curation,
# exclusions, multiple imputation, cohort construction (UK Biobank, HRS, and ELSA),
# survival modeling (Cox/Gompertz), figure generation, and table output. To reproduce
# the analyses you must (i) have licensed access to the raw UK Biobank, HRS, and ELSA
# data with the required variables (or update the alias maps to your local column names);
# and (ii) install the referenced R packagesSome steps (e.g.,
# multiple imputation and parametric survival fits) are computationally intensive
#adjust memory/parallel settings as needed before running the full workflow.