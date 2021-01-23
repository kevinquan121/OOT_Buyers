# Out-of-town Home Buyers and City Welfare (Favilukis and Van Nieuwerburgh forthcoming)
This repository contains all the code files required to generate the tables and figures in the paper, Out-of-town Home Buyers and City Welfare, forthcoming in the Journal of Finance. To quantify the welfare effects of out-of-town (OOT) home buyers, the paper develops an equilibrium model and calibrates the model to the typical U.S. metropolitan area. In the baseline model, the paper solves a heterogeneous agent model with two residential zones, city urban core and its periphery. The model consists of five sectors, households, construction firms in the two zones, consumption good firms, and out-of-twon home buyers. The main code, oot.f, is written in Fortran, and we recommend you run it on a university-level research grid or any cloud computing platforms since the computation takes up a lor of memory and the model takes a long time to compute and converge.

## Step 1: Calibration of Baseline Model (Section 4)
In this step, the main code file, "oot.f", and all the other input files are located in the folder, "baseline_model". We recommend you use the Intel Fortran Compiler and run the program on a cloud computing platform/university research grid since it takes up a significant amount of memory and time. The program will generate three output files, "output00.m", "output01.m", and, "output02.m", which will be used to generate tables in the next step. You can always skip this step and make use of the generated output files in the "Output" subfolder.

If you need a brief introduction or crash course on coputation in Fortran, we would refer you to the following resources, 

A quantitative economics class taught by Jack Favilukis: https://sites.google.com/site/jackfavilukis/teaching/comm590



Now we give a short introduction to the files in this folder. 


We need two external library 


## tfffff
