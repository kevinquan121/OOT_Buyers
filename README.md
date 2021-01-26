<p style='text-align: justify;'>

# Out-of-town Home Buyers and City Welfare (Favilukis and Van Nieuwerburgh forthcoming)
This repository contains all the code files required to generate the tables and figures in the paper, Out-of-town Home Buyers and City Welfare, forthcoming in the Journal of Finance. To quantify the welfare effects of out-of-town (OOT) home buyers, the paper develops an equilibrium model and calibrates the model to the typical U.S. metropolitan area. 

## Step 1: Calibration of Baseline Model (Section 4)
In this step, we need the folder, "Baseline_Model", which contains the main code file, "oot.f", and all the other input files. We recommend you use the Intel Fortran Compiler and run the program on a cloud computing platform/university research grid since it takes up a significant amount of memory and time. 

The program will generate three output files, "output00.m", "output01.m", and, "output02.m", which will be used to generate tables and figures in the next step. The main code file, "oot.f", contains detailed comments next to each block of code so that it is much easier for readers to follow the logic of the calibration. 

Note that we need two external libraries, "libLAPACK.f" and "libSLATEC.f", which have been included in the folder.

## Step 2: Post-Calibration Analysis (Section 5)
With the output files from Step 1, we use the MATLAB code, "ModelOfCity.m", to produce tables and figures. The MATLAB code will also produce several macro commands for the LaTex file, "OOT_zones.tex". The macro commands are used to populate the numbers in the tables so that we don't need to input those numbers manually. We store the macro commands in several LaTex files in the folder, "Figures", and they will be called in the main LaTex file, "OOT_zones.tex".

## Step 3: Couterfactual Analysis (Section 6 and Section 7)
In this step, we create several counterfactual scenarios by tuning the parameters (but we do not recalibrate) in the model. We take a deep dive into the mechanisms of the model and study the various factors that drive the results. To run the cases in this section, we need to make several minor changes to the main code, "oot.f". The various cases are displayed in Table 2 in the paper. 

## Step 4: Luxury Housing (Section 8)
In this step, the model is recalibrated to incorporate an additional residential zone, luxury housing. The code files are included in a separate folder, "Luxury_Housing". The way to solve this variation of the baseline model is the same as before. The MATLAB code needed for the post-computation analysis is "ModelOfCity_luxury.m".

## Other Resources:
If you need a brief introduction or crash course on computation in Fortran, please refer to the following resources, 

A quantitative economics class taught by Jack Favilukis: https://sites.google.com/site/jackfavilukis/teaching/comm590

</p>
