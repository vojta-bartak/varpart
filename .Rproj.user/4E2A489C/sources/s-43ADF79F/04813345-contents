library(tidyverse)
library(dplyr)
library(ggforce)
library(sf)
library(eulerr)

# radius of a circle of a given area
c_r <- function(area){
  sqrt(area/pi)
}

# area of an intersection of two circles
i_area <- function(r1, r2, d){
  suppressWarnings(case_when(
    d < abs(r1 - r2) ~ min(pi*r1^2, pi*r2^2),
    d > (r1 + r2) ~ 0,
    TRUE ~ (r2^2)/cos((d^2-r1^2+r2^2)/(2*r2*d)) + (r1^2)/cos((d^2+r1^2-r2^2)/(2*r1*d)) - sqrt((2*r2*d)^2-(d^2+r2^2-r1^2)^2)/2
  ))
}

# distance of two circles of given radii and intersection area
find_d <- function(area, r1, r2){
  f <- function(d) abs(i_area(r1, r2, d) - area)
  optimize(f, c(0, r1+r2))$minimum
}

# point at a given distance from a point in a direction of another point
point_at_dist <- function(x1, x2, d){
  dist <- sqrt((x2[1]-x1[1])^2 + (x2[2]-x1[2])^2)
  t <- d/dist
  c((1-t)*x1[1]+t*x2[1], (1-t)*x1[2]+t*x2[2])
}

#' Explained deviance of a model using the simple McFadden formula.
#'
#' @param model Model object with deviance and null.deviance names.
#' @return The fraction of the model's null deviance explained by all model predictors.
#' @export
rsq <- function(model) 1-model$deviance/model$null.deviance

#' Explained deviance of a group of predictors.
#'
#' @param model Model object with deviance and null.deviance names.
#' @param group Character vector with names of the predictors to be evaluated.
#' @return The fraction of the model's deviance explained by the given group of predictors.
#' @export
dev.expl <- function(model, group) rsq(model) - rsq(update(model, paste("~.-", paste(group, collapse = "-"))))

#' Deviance partitioning for three groups of predictors.
#'
#' @param model Model object with deviance and null.deviance names.
#' @param A Character vector with names of the predictors of the first group.
#' @param B Character vector with names of the predictors of the second group.
#' @param C Character vector with names of the predictors of the third group.
#' @param labels Character vector with group labels. The default labels are "A", "B", and "C".
#' @param sep Character used to construct labels for different group intersections.
#' @return Numeric vector with the following 8 elements:
#' 1. Deviance only explained by A
#' 2. Deviance only explained by B
#' 3. Deviance only explained by C
#' 4. Deviance not explained by C, but not allowing being attributed unambiguously to A or B
#' 5. Deviance not explained by B, but not allowing being attributed unambiguously to A or C
#' 6. Deviance not explained by A, but not allowing being attributed unambiguously to B or C
#' 7. Deviance explained by A or B or C, without allowing being attributed unambiguously to any of them
#' 8. Unexplained part of the deviance
#'
#' The elements are named based on the labels: "A", "B", "C", "A&B", "A&C", "B&C", "A&B&C", "Unexplained".
#' @export
devpart <- function(model, A, B, C, labels=c("A","B","C"), sep="&"){

  # deviance partitioning
  dev.expl(m, A) + dev.expl(m, B)
  dev.expl(m, c(A,B))

  a <- dev.expl(model, A)
  b <- dev.expl(model, B)
  c <- dev.expl(model, C)
  ab <- dev.expl(model, c(A,B)) - a - b
  ac <- dev.expl(model, c(A,C)) - a - c
  bc <- dev.expl(model, c(B,C)) - b - c
  abc <- dev.expl(model, c(A,B,C)) - a - b - c - ab - ac - bc
  unex <- 1 - rsq(model)

  rest <- get_terms(model) %>% "["(!. %in% c(A,B,C))
  if (length(rest) > 0) warning("Model terms ", paste(rest, collapse = ", "), " remained in the model!")


  names <- c(lapply(1:3, function(i)
    combn(labels, i) %>% apply(2, function(col) paste(col, collapse = sep))
  ) %>% unlist, "Unexplained")
  c(a, b, c, ab, ac, bc, abc, unex) %>% setNames(names)
}

get_polygons <- function(pars){
  require(sf)
  x11 <- pars[1]
  x12 <- pars[2]
  x21 <- pars[3]
  x22 <- pars[4]
  x31 <- pars[5]
  x32 <- pars[6]
  r1 <- pars[7]
  r2 <- pars[8]
  r3 <- pars[9]
  cA <- st_buffer(st_point(c(x11, x12)), dist = r1)
  cB <- st_buffer(st_point(c(x21, x22)), dist = r2)
  cC <- st_buffer(st_point(c(x31, x32)), dist = r3)
  pAB_ABC <- st_intersection(cA, cB)
  pBC_ABC <- st_intersection(cB, cC)
  pAC_ABC <- st_intersection(cA, cC)
  pABC <- st_intersection(pAB_ABC, st_intersection(pBC_ABC, pAC_ABC))
  pAB <- st_difference(pAB_ABC, pABC)
  pBC <- st_difference(pBC_ABC, pABC)
  pAC <- st_difference(pAC_ABC, pABC)
  pA <- st_difference(cA, st_union(cB, cC))
  pB <- st_difference(cB, st_union(cA, cC))
  pC <- st_difference(cC, st_union(cA, cB))
  list(pA,pB,pC,pAB,pAC,pBC,pABC)
}

get_areas <- function(pars, method=c("polygons", "mc"), npoints){
  if (method=="polygons"){
    require(sf)
    pols <- get_polygons(pars)
    areas <- sapply(pols, st_area)
  } else if (method == "mc"){
    xmin <- min(pars[c(1,3,5)]) - max(pars[7:9])
    xmax <- max(pars[c(1,3,5)]) + max(pars[7:9])
    ymin <- min(pars[c(2,4,6)]) - max(pars[7:9])
    ymax <- max(pars[c(2,4,6)]) + max(pars[7:9])
    big_area <- (xmax - xmin)*(ymax - ymin)
    xs <- runif(npoints, xmin, xmax)
    ys <- runif(npoints, ymin, ymax)
    pA <- sqrt((xs-pars[1])^2 + (ys-pars[2])^2) <= pars[7]
    pB <- sqrt((xs-pars[3])^2 + (ys-pars[4])^2) <= pars[8]
    pC <- sqrt((xs-pars[5])^2 + (ys-pars[6])^2) <= pars[9]
    pABC <- pA & pB & pC
    a <- mean(pA & !pB & !pC)*big_area
    b <- mean(pB & !pC & !pA)*big_area
    c <- mean(pC & !pB & !pA)*big_area
    ab <- mean(pA & pB & !pABC)*big_area
    ac <- mean(pA & pC & !pABC)*big_area
    bc <- mean(pB & pC & !pABC)*big_area
    abc <- mean(pABC)*big_area
    areas <- c(a,b,c,ab,ac,bc,abc)
  }
  areas
}

get_initial_pars <- function(parts){
  a <- parts[1]
  b <- parts[2]
  c <- parts[3]
  ab <- parts[4]
  ac <- parts[5]
  bc <- parts[6]
  abc <- parts[7]

  # radii of the circles
  r1 <- c_r(a + ab + ac + abc)
  r2 <- c_r(b + ab + bc + abc)
  r3 <- c_r(c + bc + ac + abc)

  # distances between circles
  # d12 <- find_d(ab+abc, r1, r2)
  # d13 <- find_d(ac+abc, r1, r3)
  # d23 <- find_d(bc+abc, r2, r3)
  d12 <- r1 + r2
  d13 <- r1 + r3
  d23 <- r2 + r3

  # coordinates of the centers if the circles
  x1 <- c(0,0)
  x2 <- c(d12, 0)
  cx <- (d13^2+d12^2-d23^2)/(2*d12)
  x3 <- c(
    cx,
    sqrt(d13^2 - cx^2)
  )

  c(x1[1], x1[2], x2[1], x2[2], x3[1], x3[2], r1, r2, r3)
}

get_venns_slow <- function(parts, method, npoints){
  inits_orig <- get_initial_pars(parts)
  os <- lapply(1:3, function(which_opt){
    inits <- inits_orig
    # which_opt <- c(3,2,1)[which(parts[4:6]==min(parts[4:6]))][1]
    # which_opt <- which(inits[7:9]==min(inits[7:9]))
    which_pars_opt <- list(c(1:2), c(3:4), c(5:6))[[which_opt]]
    other_pars <- c(1:9)[-which_pars_opt]
    which_pols <- case_when(which_opt == 1 ~ c(1,4,5,7),
                            which_opt == 2 ~ c(2,4,6,7),
                            which_opt == 3 ~ c(3,5,6,7))
    difference <- function(x){
      inits[which_pars_opt] <- x
      areas <- get_areas(inits, method, npoints=npoints)[which_pols]
      sum(abs(areas - parts[which_pols]))
    }

    r <- pars[7:9][which_opt]
    x1 <- inits[other_pars][1]
    y1 <- inits[other_pars][2]
    x2 <- inits[other_pars][3]
    y2 <- inits[other_pars][4]
    r1 <- inits[other_pars][5:7][-which_opt][1]
    r2 <- inits[other_pars][5:7][-which_opt][2]
    # o <- optim(c(inits[which_pars_opt]), difference, other_two=inits[other_pars], pol_inds=which_pols, which_opt)
    xmin <- min(x1-r1, x2-r2) - r
    xmax <- max(x1+r1, x2+r2) + r
    ymin <- min(y1-r1, y2-r2) - r
    ymin <- min(y1-r1, y2-r2) - r

    # xs <- runif(1e4, xmin, xmax)
    # ys <- runif(1e4, ymin, ymax)
    # values <- sapply(1:length(xs), function(i){
    #   if (((xs[i]-x1)^2+(ys[i]-y1)^2 <= (r+r1)^2) &
    #       ((xs[i]-x2)^2+(ys[i]-y2)^2 <= (r+r2)^2)) {
    #     inits[which_pars_opt] <- c(xs[i], ys[i])
    #     areas <- get_areas(inits, method, npoints=npoints)[which_pols]
    #     sum(abs(areas - parts[which_pols]))
    #   } else {
    #     NA
    #   }
    # })
    # value <- min(values, na.rm = T)
    # ind <- which(values==value)
    # o <- list(par = c(xs[ind], ys[ind]), value=value)

    o <- nloptr::nloptr(x0 = c(inits[which_pars_opt]),
                        eval_f = difference,
                        lb = c(xmin, ymin),
                        ub = c(xmax, ymax),
                        eval_g_ineq <- function(x) {
                          c((r+r1)^2 - (x[1]-x1)^2 - (x[2]-y1)^2, (r+r2)^2 - (x[1]-x2)^2 - (x[2]-y2)^2)},
                        opts = list(
                          "algorithm" = "NLOPT_LD_MMA",
                          "xtol_rel"=1.0e-12
                        )
    )
    list(par=o$solution, value=o$objective)
  })
  vals <- sapply(os, function(o) o$value)
  which_opt <- which(vals==min(vals))
  o <- os[[which_opt]]
  which_pars_opt <- list(c(1:2), c(3:4), c(5:6))[[which_opt]]
  perc_diff <- round(100*o$value/sum(parts), 2)
  print(paste("Minimized percentual area difference", perc_diff, "%"))
  inits_orig[which_pars_opt] <- o$par
  list(parts = parts,
       pars = inits_orig)
}

get_venns_2p <- function(parts, npoints){
  inits <- get_initial_pars(parts)

  diff <- function(x){
    inits[1:4] <- x
    areas <- get_areas(inits, "mc", npoints=npoints)
    sum(abs(areas - parts[1:7]))
  }

  xmin <- inits[5] - inits[9] - 2*(inits[7] + inits[8])
  xmax <- inits[5] + inits[9] + 2*(inits[7] + inits[8])
  ymin <- inits[6] - inits[9] - 2*(inits[7] + inits[8])
  ymax <- inits[6] + inits[9] + 2*(inits[7] + inits[8])
  o <- nloptr::mma(x0=inits[1:4], fn=diff, lower = c(xmin, ymin, xmin, ymin), upper = c(xmax, ymax, xmax, ymax),
                   hin = function(x) {
                     c(
                       (inits[7]+inits[8])^2 - ((x[1] - x[3])^2 + (x[2]-x[4])^2),
                       (inits[7]+inits[9])^2 - ((x[1] - inits[5])^2 + (x[2]-inits[6])^2),
                       (inits[8]+inits[8])^2 - ((x[3] - inits[5])^2 + (x[4]-inits[6])^2)
                     )},
                   control = list("xtol_rel"=1.0e-12))
  inits[1:4] <- o$par
  list(parts = parts,
       pars = inits)
}

#' Computes the Venn's/Euler's diagrams for a given deviance partitioning as returned by the function devpart.
#'
#' @param parts Numeric vector of length 8, with deviance partitioning as returned by the function devpart.
#' @param method Character specifying the method used to optimize the size and position of diagram circles. One of "eulerr" (default), "mc", "polygons", "venneuler" (See Details).
#' @param npoints Integer specifying the number of random points used in the method "mc" for Monte Carlo estimation of areas of circles' intersections. Deafult is 10,000.
#' @param min_share Numeric specifying the minimum area of intersection (in the explained-deviance units), which is taken into account in the optimization. Experimenting with this parameter is recommended to get optimal result.
#' @details Method "eulerr" (deafult) uses the package eulerr (Larsson, 2022). It is the fastest method usually with the best result.
#' Method "mc" first identifies the size of all circles and then uses nloptr package (Steven G. Johnson, https://nlopt.readthedocs.io/en/latest/) to optimize their positions. The MMA optimization algorithm is used, which allows for inequality constraints ensuring all three circles have nonzero intersection. The area of each particular solution is estimated using the Monte Carlo method, with the number of random points determined by the npoints parameter.
#' Method "polygons" is similar to the "mc", but the area of individual polygons is determined using the sf package (Pebesma, 2018). This method is slow and is not recommended.
#' Method "venneuler" uses the venneuler package (Wilkinson, 2022) to optimize the circles' parameters. It is relatively fast, but the results are usually suboptimal compared to the eulerr method. It relies on a Java library, which can cause problems.
#' After the computation, the solution is evaluated based on percentual overlap with the required intersections. This information is printed.
#' @return A list of two elements:
#' parts ... numeric vector with the input deviance partitioning, with the negative values set to zero.
#' pars ... numeric vector with parameters of the optimized circles corresponding as much as possible to the input deviance partitioning.
#' @export
get_venns <- function(parts, method=c("eulerr", "mc", "polygons", "venneuler"), npoints=1e4,
                      min_share = NULL){
  method <- method[1]
  if (is.null(min_share) & method == "euler") min_share <- 0
  orig_parts <- parts
  orig_parts[orig_parts < 0] <- 0
  if (!is.null(min_share)) parts[parts < min_share] <- min_share

  venns <- if(method == "mc"){
    get_venns_2p(parts, npoints=npoints),
  } else if(method == "polygons"){
    get_venns_slow(parts, "polygons"),
  } else if(method == "venneuler"){
    require(venneuler)
    combs <- lapply(1:3, function(i)
      combn(1:3, i) %>%
        apply(2, function(col) paste(col, collapse = "&"))
    ) %>% unlist
    v <- venneuler(combs, parts[1:7])
    list(parts = parts,
         pars = c(v$centers %>% apply(1, function(i) list(i)) %>% unlist, v$diameters/2))
  } else if (method == "eulerr"){
    require(eulerr)
    combs <- lapply(1:3, function(i)
      combn(1:3, i) %>%
        apply(2, function(col) paste(col, collapse = "&"))
    ) %>% unlist
    e <- euler(parts[1:7] %>% set_names(combs))$ellipses
    list(parts = orig_parts,
         pars = c(e[1,"h"], e[1,"k"], e[2,"h"], e[2,"k"], e[3,"h"], e[3,"k"], e[1,"a"], e[2,"a"],e[3,"a"]))
  }
  perc_diff <- round(100*get_areas(venns$pars, method="mc")/sum(venns$parts[1:7]), 2)
  print(paste("Minimized percentual area difference", perc_diff, "%"))
  return(venns)
}

get_label_coords <- function(pars){
  centr <- c(mean(pars[c(1,3,5)]), mean(pars[c(2,4,6)]))
  incr <- max(pars[c(7,8,9)])*0.1
  x1 <- c(point_at_dist(pars[1:2], centr, -pars[7]+incr))
  x2 <- c(point_at_dist(pars[3:4], centr, -pars[8]+incr))
  x3 <- c(point_at_dist(pars[5:6], centr, -pars[9]+incr))
  data_frame(X = c(x1[1], x2[1], x3[1]), Y = c(x1[2], x2[2], x3[2]))
}

#' Plot the Venn's/Euler's diagramms.
#'
#' @param venns A list of two numeric vectors as returned by the function get_venns.
#' @param labels Character vector of group labels thaht will appear as labels in the plot.
#' @param cols Character vector specifying the colors used to fill the circles.
#' @param expand Numeric vector of length two, with a fraction by which the plot window should be extended in x and y directions in order to include all the labels. Default is 0.1 and 0.1 (i.e. 10% expansion in both directions).
#' @param hjust Numeric vector of length three, specifying the horizonthal adjustments of the group labels (i.e. the relative positions of the anchor points of the labels, with 0 ... anchor point is at the left edge of the label, 1 ... anchor point is at the right edge of the label). Values can exceed the (0, 1) interval.
#' @param vjust Numeric vector of length three, specifying the vertical adjustments of the group labels (i.e. the relative positions of the anchor points of the labels, with 0 ... anchor point is at bottom edge of the label, 1 ... anchor point is at the top edge of the label). Values can exceed the (0, 1) interval.
#' @param unexpl.position Character of length two, specifying the relative position of the label for the unexplained part of the deviance in the plot, in x and y direction. (0, 0) means lower left corner, (1, 1) means upper right corner. Values can exceed the (0, 1) interval.
#' @param alpha Numeric value between 0 and 1 specifying the transparency of the circles. The default is 0.4.
#' @return A ggplot object visualizing the input deviance partitioning using three intersecting circles with areas of all parts optimized to reflect the deviance partitioning.
#' @export
plot_venns <- function(venns, labels=c("A","B","C"), cols=c("red","green","blue"),
                       expand=c(0.1,0.1), hjust=NULL, vjust=NULL,
                       unexpl.position = c(1,0), alpha=0.4){
  pars <- venns$pars
  parts <- venns$parts
  if (is.null(hjust)) hjust <- c(1,0,0.5)
  if (is.null(vjust)) vjust <- c(0.5,0.5,0)
  x11 <- pars[1]
  x12 <- pars[2]
  x21 <- pars[3]
  x22 <- pars[4]
  x31 <- pars[5]
  x32 <- pars[6]
  r1 <- pars[7]
  r2 <- pars[8]
  r3 <- pars[9]

  xmin <- min(pars[c(1,3,5)]-pars[7:9])
  xmax <- max(pars[c(1,3,5)]+pars[7:9])
  ymin <- min(pars[c(2,4,6)]-pars[7:9])
  ymax <- max(pars[c(2,4,6)]+pars[7:9])
  x_unex <- (xmin + unexpl.position[1]*(xmax - xmin))
  y_unex <- (ymin + unexpl.position[2]*(ymax - ymin))
  # hj_unex <- unexpl.position[3]
  # vj_unex <- unexpl.position[4]


  pols <- get_polygons(pars)
  txt_coords <- lapply(pols, st_centroid) %>% lapply(st_coordinates) %>% lapply(as_tibble) %>% bind_rows
  ggplot(data.frame(x=c(x11, x21, x31),
                    y=c(x12, x22, x32),
                    r=c(r1, r2, r3)) %>% cbind(get_label_coords(pars))) +
    geom_circle(aes(x0=x,y0=y,r=r,fill=labels), alpha=alpha, color=NA) +
    geom_label(aes(x=X, y=Y), label=labels, hjust=hjust, vjust=vjust) +
    geom_text(data=txt_coords, aes(x=X, y=Y), label=paste(round(parts[1:7]*100, 1), "%")) +
    annotate(geom="text", x=x_unex, y=y_unex, #hjust=hj_unex, vjust=vj_unex,
             label=paste("Unexplained: ", round(parts[8]*100, 1), "%")) +
    coord_fixed() +
    theme_void() +
    scale_fill_manual(values=cols) +
    scale_y_continuous(expand = expansion(mult=expand[2])) +
    scale_x_continuous(expand = expansion(mult=expand[1])) +
    theme(legend.position = "None")
}


get_terms <- function(model, pattern=NULL){
  terms <- attr(terms(model), "term.labels")
  if (!is.null(pattern)) {
    inds <- lapply(pattern, function(pat) grep(pat, terms)) %>% unlist %>% unique
    terms <- terms[inds]
  }
  terms
}
