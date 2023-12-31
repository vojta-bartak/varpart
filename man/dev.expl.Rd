% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/varpart.R
\name{dev.expl}
\alias{dev.expl}
\title{Explained deviance of a group of predictors.}
\usage{
dev.expl(model, group)
}
\arguments{
\item{model}{Model object with deviance and null.deviance names.}

\item{group}{Character vector with names of the predictors to be evaluated.}
}
\value{
The fraction of the model's deviance explained by the given group of predictors.
}
\description{
Explained deviance of a group of predictors.
}
