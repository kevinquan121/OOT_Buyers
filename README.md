# Out-of-town Home Buyers and City Welfare (Favilukis and Van Nieuwerburgh forthcoming)
This repository contains all the code files required to generate the tables and figures in the paper, Out-of-town Home Buyers and City Welfare, forthcoming in the Journal of Finance. To quantify the welfare effects of out-of-town (OOT) home buyers, the paper develops an equilibrium model and calibrates the model to the typical U.S. metropolitan area. In the baseline model, the paper solves a heterogeneous agent model with two residential zones, city urban core and its periphery. The model consists of five sectors, households, construction firms in the two zones, consumption good firms, and out-of-twon home buyers. The main code, oot.f, is written in Fortran, and we recommend you run it on a university-level research grid or any cloud computing platforms since the computation takes up a lor of memory and the model takes a long time to compute and converge.

## Step 1: Calibration of Baseline Model (Section 4)
In this step, we need the folder, "Baseline_Model", which contains the main code file, "oot.f", and all the other input files. We recommend you use the Intel Fortran Compiler and run the program on a cloud computing platform/university research grid since it takes up a significant amount of memory and time. The program will generate three output files, "output00.m", "output01.m", and, "output02.m", which will be used to generate tables and figures in the next step. The main code file, "oot.f", contains detailed comments next to each block of code so that it is much easier for readers to follow the logic of the calibration. You can always skip this step and make use of the output files generated by the authors in the "Output" subfolder.

Note that we need two external libraries, "libLAPACK.f" and "libSLATEC.f", which have been included in the folder.

comment out code to calibrate

## Step 2: Post-Calibration Analysis (Section 5)
With the output files from Step 1, we use the Matlab code, "ModelOfCity.m", to produce tables and figures. 


## Step 3: Couterfactual Analysis (Section 6 and Section 7)
In this step, we create several counterfactual scenarios by tuning the parameters (but we do not recalibrate) in the model. We take a deep dive into the mechanisms of the model and study the various factors that drive the results. To run the cases in this section, we need to make several minor changes to the main code, "oot.f". The edited code files are included in the folder "Counterfactuals". Simply replace "oot.f" in the "Baseline_Model" folder with the 


## Step 4: Luxury Housing (Section 8)
in this step, the model is recalibrated to incorporate an additional residential zone, luxury housing. The code files are included in a separate folder, "Luxury_Housing". The way to solve the model and do post-computation analysis is the same as the baseline mdoel. 

## Other Resources:
If you need a brief introduction or crash course on coputation in Fortran, we would refer you to the following resources, 

A quantitative economics class taught by Jack Favilukis: https://sites.google.com/site/jackfavilukis/teaching/comm590
