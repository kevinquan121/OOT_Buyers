%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%this uses output from fortran to produce summary statistics%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clear
% Choose which tables or figures to generate
mode=1; %1 for table 1 & 2; 2 for table 3; 3 for table 4.

if mode==1
    model_space=["Baseline", "NoZoneTwoOOT", "OOTUpFifty", "OOTDownFifty", "AltOOTB", "PersistHigh", "PersistLow",...
    "OOTRentOut", "OOTRentOutSixFour", "SameBeta", "LTVHigh", "LTVlow", "HBarZOneEZTwo","HBarZOneDownFifty",...
    "HighDemandE", "MedDemandE", "LowDemandE", "ProfitRedist", "NoHresMin", "NoShiftThresh", "OnlyOwners",...
    "OOTTaxtoLowProdPanelB","OOTTaxtoLowProdPanelC", "OOTTaxtoLowProdPanelD", "Luxury"];
elseif mode==2
    tax_space=["0","1","2","346","5","75","10"];
    theta_space=["0","075","115","155"];
%    theta_space=["115","155"];
%    b_space=["64"];
    b_space=["06","64"];
%    b_space=["64"];
    name_sequence=["one","two", "three", "four", "five", "six", "seven"];
    table3_space=[];
    latex_macro_name=[];
    for i=1:length(b_space)
        temp_name1=join(["b",b_space(i)],"");
        temp_macro_name1=join(["b",name_sequence(i)],"");
        for j=1:length(theta_space)
            temp_name2=join([temp_name1,"theta",theta_space(j)],"");
            temp_macro_name2=join([temp_macro_name1,"theta",name_sequence(j)],"");
            for k=1:length(tax_space)
                temp_name3=join([temp_name2,"tax",tax_space(k)],"");
                temp_macro_name3=join([temp_macro_name2,"tax",name_sequence(k)],"");
                table3_space=[table3_space temp_name3];
                latex_macro_name=[latex_macro_name temp_macro_name3];
            end
        end
    end
    model_space=table3_space;
else
    tax_space=["0","1","2","346","5","75","10"];
    b_space=["06","64"];
    ite_space=["1","2","3","4","5"];
    name_sequence=["one","two", "three", "four", "five", "six", "seven"];
    table4_space=[];
    latex_macro_name=[];
    for i=1:length(b_space)
        temp_name1=join(["b",b_space(i)],"");
        temp_macro_name1=join(["b",name_sequence(i)],"");
        for j=1:length(tax_space)
            temp_name2=join([temp_name1,"tax",tax_space(j)],"");
            temp_macro_name2=join([temp_macro_name1,"tax",name_sequence(j)],"");
            for k=1:length(ite_space)
                temp_name3=join([temp_name2,"\",ite_space(k)],"");
                table4_space=[table4_space temp_name3];
                latex_macro_name=[latex_macro_name temp_macro_name2];
            end
        end
    end
    model_space=table4_space;
end

%model_space=["b06theta0tax0", "b06theta075tax0", "b06theta115tax0", "b06theta155tax0" ];

% Start computating statistics
%for model=1
for model=length(model_space)
    
path="../Fortran Output/";
% Initialize Statistics
fracRet=0; AvgHours=0; HoursMinBind=0; RetInc=0; RetIncbyLabInc=0; HousTotConsratio=0; NWbyInc=0; GiniNW=0; GiniInc=0;
Probbequest=0; fracbeqann=0; fracRetRel=0; IncRel=0; MedMktRentbySqftRel=0; HORel=0; cbarFrac=0; MedMktPHbyMedMktRent=0;
OwnRate=0; OwnRateBefore=0; OwnRateAfter=0; NWindMid1Ch1=0; WageIndMid1Ch1=0; OwnLocalChangeZ1=0; OwnLocalChangeZ2=0; SizeChShort=0;
SizeChLong=0; WageChShort=0; WageChLong=0; FracConstructChShort=0; FracConstructBefore=0; FracConstructAfter=0; HoursWorkedChange=0; EarningsChange=0;
dE=zeros(20,1); dErenter=zeros(20,1); dEowner=zeros(20,1); % change in earnings by age group
x1=zeros(1,22); x2=zeros(1,15);
Age2OwnHurt=0; Age14OwnHurt=0; AvgBenefit=0; AvgOwnBenefit=0; AvgRentBenefit=0;
for version=0
if mode==1
    location=join([path,"Table2/",num2str(model_space(model)),"/version",num2str(version)],"");
elseif mode==2
    location=join([path,"Table3/",num2str(model_space(model))],"");
else
    location=join([path,"Table4/",num2str(model_space(model))],"");
end
cd(location)

%Check whether the current folder is empty, and if empty, skip current iteration.
% [~,list] = system('dir /S *.m');
% result = textscan(list, '%s', 'delimiter', '\n');
% fileList = result{1};
% if length(fileList)<=3
%     continue
% end

%Add function paths
addpath('../Functions')

%Input Calibration Results
output00
out=[temp1 temp2 temp3 temp4 temp5]; disp(out(1:10,2));
output02;
outErr=temp1; disp(mean(abs(outErr(101:end,:))));
clear temp*
output01;

Theta=1.15;

%Set Parameters: time lengeth 2000 periods, number of agents 500, and age of agents in 21-100
T=length(out); nAgent=length(outInd)/T; nAge=max(outInd(:,3)); 

%%%Clean Macro Variables%%%

[a, b]=size(taxpropOOT); if b==1; taxpropOOT=ones(1,2)*taxpropOOT; end
[a, b]=size(taxprop); if b==1; taxprop=[taxprop taxprop]; end
%outInd=out3; clear out3;
% if exist('RTSH1loc1')==1; H1bar=RTSH1loc1; else; if length(HBARloc1)==1; H1bar=HBARloc1; else; H1bar=HBARloc1(out(:,1)); [a b]=size(H1bar); if a<T; H1bar=H1bar'; end; end; end;
% if exist('RTSH1loc2')==1; H2bar=RTSH1loc2; else; if length(HBARloc2)==1; H2bar=HBARloc2; else; H2bar=HBARloc2(out(:,1)); [a b]=size(H2bar); if a<T; H2bar=H2bar'; end; end; end;
% RTSHloc1=RTSH0loc1; RTSHloc2=RTSH0loc2;
if length(deprH)==1; deprH(2)=deprH(1); end
%RCrentred=[.5 .5];
high=out(:,1)==2;
low=out(:,1)==1;
ForDemTot(:,1)=exp(HFgrid0(out(:,1),1)-HFgrid1(out(:,1),1).*log(out(:,10).*(1+taxpropOOT(1)))); %this is foreign demand per capita in Z1
ForDemTot(:,2)=exp(HFgrid0(out(:,1),2)-HFgrid1(out(:,1),2).*log(out(:,11).*(1+taxpropOOT(2)))); %this is foreign demand per capita in Z2
OOT1=mean(ForDemTot(high,1)./out(high,7)); %share of OOT demand in Z1
OOT2=mean(ForDemTot(high,2)./out(high,8)); %share of OOT demand in Z2
% computeOOT1(-5.746, high, HFgrid1(out(:,1),1), out(:,10), out(:,7), taxpropOOT(1))
% computeOOT2(-3.328, high, HFgrid1(out(:,1),2), out(:,11), out(:,8), taxpropOOT(1))
% 
% computeOOT1(-4.617, high, HFgrid1(out(:,1),1), out(:,10), out(:,7), taxpropOOT(1))
% computeOOT2(-3.34, high, HFgrid1(out(:,1),2), out(:,11), out(:,8), taxpropOOT(1))
% 

P1_high=mean(out(high,10));
P2_high=mean(out(high,11));
P1_low=mean(out(low,10));
P2_low=mean(out(low,11));
H1_high=mean(out(high,7));
H2_high=mean(out(high,8));
Z1HIncrease=(mean(out(high,7))-mean(out(low,7)))/mean(ForDemTot(high,1));


exp0=1/((1-gamma0)*(1-alphaN));
AgeProd0=[0.4088    0.6375    0.8236    0.9262    1.0139    1.1078    1.1771    1.2848    1.2481    1.2298    1.1425    0.0000    0.0000    0.0000    0.0000    0.0000    0.0000    0.0000    0.0000    0.0000];
AgeProd2=[0.4088    0.6375    0.8236    0.9262    1.0139    1.1078    1.1771    1.2848    1.2481    1.2298    1.1425    0.8304    0.6355    0.5093    0.4006    0.0000    0.0000    0.0000    0.0000    0.0000];
AgeProd3=[0.4088    0.6375    0.8236    0.9262    1.0139    1.1078    1.1771    1.2848    1.2481    1.2298    1.1425    1.0380    0.7944    0.6366    0.5008    0.0000    0.0000    0.0000    0.0000    0.0000];
AgeProd=AgeProd0;
outnext=[out(2:T,:); zeros(1,50)];
nDZ=length(DZgrid);
if length(taxprop)==1; taxpropTimeSeries=taxprop*ones(T,1); else; taxpropTimeSeries=taxprop(out(:,1),:); end;


IncStates=mean(DZgrid(1:(nDZ-nRet),:)); %three income states
TrHFProb=0.9; %OOT transition probability
Wage=out(:,2);
H1=out(:,7); H1last=[mean(H1); H1(1:T-1)]; 
H2=out(:,8); H2last=[mean(H2); H2(1:T-1)]; 
PH1=out(:,10); 
PH2=out(:,11);
Rent1=out(:,3); 
Rent2=out(:,4);
% tempR1=1.0-H1./H1bar;
% tempR2=1.0-H2./H2bar;
% HoursDemandC=(RTSC./Wage).^(1.0/(1.0-RTSC)); %this is aggregate, productivity adjusted hours demand, scaled by number of households
% HoursDemandLOC1=(tempR1.*RTSHloc1.*out(:,26)./Wage).^(1.0/(1.0-RTSHloc1));
% HoursDemandLOC2=(tempR2.*RTSHloc2.*out(:,27)./Wage).^(1.0/(1.0-RTSHloc2));
% WageBillC=HoursDemandC.*Wage; %this is the aggregate wage bill scaled by number of households
% WageBillLOC1=HoursDemandLOC1.*Wage; %this is the aggregate wage bill scaled by number of households
% WageBillLOC2=HoursDemandLOC2.*Wage; %this is the aggregate wage bill scaled by number of households
PropTaxIncome=taxpropTimeSeries(:,1).*H1.*PH1+taxpropTimeSeries(:,2).*H2.*PH2+taxpropOOT(1)*ForDemTot(:,1).*PH1+taxpropOOT(2)*ForDemTot(:,2).*PH2;
tax_neutral=(taxpropTimeSeries(1,1)*sum((H1.*PH1+H2.*PH2).*low)/sum(low)-taxpropOOT(1)*sum((ForDemTot(:,1).*PH1+ForDemTot(:,2).*PH2).*high)/sum(high))/(sum((H1.*PH1+H2.*PH2).*high)/sum(high));
%PropTaxIncome=taxpropTimeSeries(:,1).*H1.*PH1+taxpropTimeSeries(:,2).*H2.*PH2;
% nAgent0=nAgent*round(mean(out(:,12)/(nAgent*mean(HoursDemandC+HoursDemandLOC1+HoursDemandLOC2)))); %this is the number of agents in fortran, for matlab we ususally get a subset only
% ProfitPerAgent=(ProfitRedist(1)*out(:,30)+ProfitRedist(2)*out(:,31)+ProfitRedist(3)*out(:,32))/nAgent0;
% GDP=mean((HoursDemandC+HoursDemandLOC1+HoursDemandLOC2).*Wage+(out(:,30)+out(:,31)+out(:,32))/2000);
% GDPnext=[GDP(2:end,:); GDP(end,:)];



%%%Clean Micro Variables%%%

Hind=zeros(T,nAgent); RenterInd=Hind; HresInd=Hind; WageInd=Hind; WelfInd=Hind; 
WelfIndAlt=Hind; AgeInd=Hind; RenterIndLast=Hind; LOCind=Hind; Bind=Hind; 
HallIndLast=Hind; Cind=Hind; HexpInd=Hind; HoursInd=Hind; HexpInd=Hind; 
Zind=Hind; NWind=Hind;  iZind=Hind; LIind=Hind; LIPTind=Hind;

for t=1:T
    in0=(t-1)*nAgent+[1:nAgent];
    WelfInd(t,:)=outInd(in0,1)';
    WelfIndAlt(t,:)=outInd(in0,2)';
    AgeInd(t,:)=outInd(in0,3)';
    RenterIndLast(t,:)=outInd(in0,4)';
    LOCind(t,:)=outInd(in0,5)';
    Bind(t,:)=outInd(in0,6)';
    Hind(t,:)=outInd(in0,7)';
    HresInd(t,:)=outInd(in0,9)';
    Cind(t,:)=outInd(in0,8)';
    HexpInd(t,:)=HresInd(t,:).*out(t,2+LOCind(t,:));
    HoursInd(t,:)=outInd(in0,10)';
    Zind(t,:)=outInd(in0,11)';
    iZind(t,:)=outInd(in0,14)';
%     if nDZ==3;
%      iZind(t,:)=1*(Zind(t,:)<(DZgrid(1)+DZgrid(2))*.5)+2*(Zind(t,:)>(DZgrid(1)+DZgrid(2))*.5 & Zind(t,:)<(DZgrid(2)+DZgrid(3))*.5)+3*(Zind(t,:)>(DZgrid(2)+DZgrid(3))*.5);
%     end;
%     if n
%      iZind(t,:)=1*(Zind(t,:)<(DZgrid(1)+DZgrid(2))*.5)+2*(Zind(t,:)>(DZgrid(1)+DZgrid(2))*.5 & Zind(t,:)<(DZgrid(2)+DZgrid(3))*.5)+3*(Zind(t,:)>(DZgrid(2)+DZgrid(3))*.5 & Zind(t,:)<(DZgrid(3)+DZgrid(4))*.5)+4*(Zind(t,:)>(DZgrid(3)+DZgrid(4))*.5);
%     end;
    RenterInd(t,:)=outInd(in0,12)';
    NWind(t,:)=outInd(in0,13)';
    WageInd(t,:)=Zind(t,:).*AgeProd(AgeInd(t,:)).*HoursInd(t,:)*out(t,2);
    PensionInd(t,:)=(AgeInd(t,:)>nAge-nRet).*out(t,20).*SSIdist(iZind(t,:));  
    in=AgeInd(t,:)<=nAge-nRet; LIind(t,in)=WageInd(t,in)*(1-taxss); LIPTind(t,in)=WageInd(t,in);
    in=AgeInd(t,:)>nAge-nRet; LIind(t,in)=PensionInd(t,in); LIPTind(t,in)=LIind(t,in);
%     ProfitInd(t,:)=ones(1,nAgent)*ProfitPerAgent(t);
%     TotIncInd(t,:)=WageInd(t,:)+(1-PriceBond)*NWind(t,:)+ProfitInd(t,:);
%     HSVtaxInd(t,:)=TotIncInd(t,:)-lambda0(out(t,1))*TotIncInd(t,:).^(1-tau0(out(t,1))); 
%     HSVtaxBaseInd(t,:)=TotIncInd(t,:)-lambdaBase*TotIncInd(t,:).^(1-tauBase); 
end



% Data
AvgMSAInc=75101; %Average household labor income in 2016 for US
AvgUSSqft=1600; %Average US housing unit size after 1960 by ACS 
AvgMSApop=6079896; %Average MSA population


%%% Calibration Results
% first 100 periods as burn-in 
in0=[1:T]'>100; in1=[1:T]'>100 & out(:,1)==1; in2=[1:T]'>100 & out(:,1)==2;
% indicator for being in the workforce: below retirement age (nRet=9, 65) and works postiive hours
inw=HoursInd>0;
inw1=inw==1 & LOCind==1;
inw2=inw==1 & LOCind==2;
%indicator for being retirees
inr=AgeInd>nAge-nRet;

% Demographics
fracRet=(fracRet*version+mean(AgeInd(in0,:)>nAge-nRet,'all'))/(version+1); %fraction of retirees

% Labor Income
% compute weights---frist average within period, then average across periods
Wt=inw./sum(inw,2); %Workers
Wt1=inw1./sum(inw1,2);
Wt2=inw2./sum(inw2,2);
Wtr=inr./sum(inr,2); %Retirees
AvgIncome=sum(Wt.*WageInd,2); %Average income per period (4yr)
AvgIncome1=sum(Wt1.*WageInd,2); %Average income per period (4yr)
AvgIncome2=sum(Wt2.*WageInd,2); %Average income per period (4yr)
AvgIncomeWorker4y=mean(AvgIncome); %Average income per period (4yr)
AvgIncomeWorker4y1=mean(AvgIncome1); %Average income per period (4yr)
AvgIncomeWorker4y2=mean(AvgIncome2); %Average income per period (4yr)
AvgIncomeWorker1y=AvgIncomeWorker4y/4;
DollarMultiplier=AvgMSAInc/AvgIncomeWorker1y; % Dollar Multiplier

RetInc=(RetInc*version+mean(sum(Wtr.*PensionInd,2))*DollarMultiplier/4)/(version+1); %Retirement Income
RetIncbyLabInc=(RetIncbyLabInc*version+mean(sum(Wtr.*PensionInd,2))/AvgIncomeWorker4y)/(version+1);

% Preferences
AvgHours=(AvgHours*version+mean(sum(Wt(in0,:).*HoursInd(in0,:),2)))/(version+1); %Average hours worked
HoursMinBind=(HoursMinBind*version+mean(HoursInd(in0,:)<AvgHours*HoursMin,'all'))/(version+1); %percent of individuals with binding min working hours
% housing consumption
RentInd=(LOCind==1).*kron(out(:,3),ones(1,nAgent))+(LOCind==2).*kron(out(:,4),ones(1,nAgent)); %individual rental price
PHind=(LOCind==1).*kron(out(:,10),ones(1,nAgent))+(LOCind==2).*kron(out(:,11),ones(1,nAgent)); %individual housing price
HCind=(HresInd).*RentInd; %individual housing consumption
HousTotConsratio=(HousTotConsratio*version+mean(HCind(in0,:)./(HCind(in0,:)+Cind(in0,:)),'all'))/(version+1); %housing consumption to total consumption
% beta
PbetaHy=(beta*BetaRel(2))^(1/4);PbetaLy=(beta*BetaRel(1))^(1/4);
% income
NWbyInc=(NWbyInc*version+mean(sum(Wt(in0,:).*NWind(in0,:),2))/AvgIncomeWorker1y)/(version+1);%wealth to income ratio
GiniNW=(GiniNW*version+gini(ones(1900,nAgent),NWind(in0,:)))/(version+1);%Gini coefficient for Wealth
GiniInc=(GiniInc*version+gini(Wt(in0,:),WageInd(in0,:)))/(version+1);%Gini coefficient for income
% bequest
AgeIndLag=lagmatrix(AgeInd,1);
NewBornInd=(AgeIndLag>=AgeInd);
NewBornByYear=sum(NewBornInd,2);
Probbequest=(Probbequest*version+mean(NewBornByYear./sum(AgeInd<=(nAge-nRet),2)))/(version+1);
NewBornByYear=sum(NewBornInd,2)/nAgent/4;
NewBorn=mean(NewBornByYear(101:end));
BequestByYear=out(:,9);
Bequest=mean(BequestByYear(101:end));
NetWealth=mean(NWind(101:end,:),'all');
fracbeqann=(fracbeqann*version+Bequest*NewBorn/NetWealth)/(version+1);
% fracRetRel
fracRetZ1=sum(inr.*(LOCind==1), 2)./sum((LOCind==1), 2);
fracRetZ2=sum(inr.*(LOCind==2), 2)./sum((LOCind==2), 2);
fracRetRel=(fracRetRel*version+mean(fracRetZ1(in0)./fracRetZ2(in0)))/(version+1);
% IncRel
IncZ1=sum(WageInd(in0,:).*(LOCind(in0,:)==1), 2)./sum(inw1(in0,:),2);
IncZ2=sum(WageInd(in0,:).*(LOCind(in0,:)==2), 2)./sum(inw2(in0,:),2);
IncRel=(IncRel*version+mean(IncZ1./IncZ2))/(version+1);
% MedMktRentbySqftRel
MedMktRentbySqftRel=(MedMktRentbySqftRel*version+mean(out(in0,3))/mean(out(in0,4)))/(version+1);
% HORel
% HOZ1=sum((LOCind(in0,:)==1).*(RenterInd(in0,:)==2),2)./sum((LOCind(in0,:)==1),2);
% HOZ2=sum((LOCind(in0,:)==2).*(RenterInd(in0,:)==2),2)./sum((LOCind(in0,:)==2),2);
% HORel=(HORel*version+mean(HOZ1./HOZ2))/(version+1);
% consumption above bar
cbarFrac=(cbarFrac*version+mean(Cind(in0,:)>0.25,'all'))/(version+1);

% Production and Housing
NormSqft = AvgUSSqft/mean(HresInd(in0,:),'all') ;  
% 1. compute average house size in each zone (hbar) and in the msa (includes owned and rented, excludes RC). The msa number is the weighted avg of the house sizes of the two zones, weighted by the number of housing units (owned and rented)
AvgH1=mean(HresInd(LOCind==1));
AvgH2=mean(HresInd(LOCind==2));
AvgH=AvgH1*mean(sum(LOCind==1,2))/nAgent+AvgH2*mean(sum(LOCind==2,2))/nAgent;
% 2. compute average house price per unit in msa as the weighted avg of the house prices per unit of the two zones, weighted by the number of housing units (owned and rented)
AvgPH1=mean(HresInd(LOCind==1))*mean(PH1);
AvgPH2=mean(HresInd(LOCind==2))*mean(PH2);
AvgPH=AvgPH1*mean(sum(LOCind==1,2))/nAgent+AvgPH2*mean(sum(LOCind==2,2))/nAgent;
% 3. compute price per foot in the msa as the ratio of average price per unit and average house size
PHSqft=AvgPH/AvgH ; 
% 4. compute mean rent per unit as R*hbar in each zone. Compute median rent  per unit in msa as the weighted avg of the house prices per unit of the two zones, weighted by the number of housing units (owned and rented)   
AvgR1=mean(HresInd(LOCind==1))*mean(Rent1);
AvgR2=mean(HresInd(LOCind==2))*mean(Rent2);
AvgR=AvgR1*mean(sum(LOCind==1,2))/nAgent+AvgR2*mean(sum(LOCind==2,2))/nAgent;
% 5. compute median rent per foot as median rent per unit divided by unit size, in every zone and for msa average
RSqft=AvgR/AvgH ; 
MedMktPHbyMedMktRent=(MedMktPHbyMedMktRent*version+4*AvgPH/AvgR)/(version+1);

% Commuting Cost
CommCostFinbyInc=CommCostFin/0.285;
CommCostFinDollar=CommCostFinbyInc*AvgMSAInc;

%%% Baseline Results
% ?Earnings, Wealth, and Home Ownership




BindNext=(NWind+LIind-Cind-RentInd.*HresInd-(RenterInd==2).*(HresInd+Hind).*(PHind-RentInd))/PriceBond;
NWindNext=BindNext+(RenterInd==2).*(HresInd+Hind).*((LOCind==1).*kron([out(2:T,10);
    mean(out(:,10))*(1-taxprop(1)-deprH(1))],ones(1,nAgent))+(LOCind==2).*kron([out(2:T,10); mean(out(:,10))*(1-taxprop(2)-deprH(2))],ones(1,nAgent)));
%BindNext and NWindNext are the bonds and wealth that will occur next period if the agent does not die and does not receive a bequest
Cagg=sum(Cind, 'all');
Propertaxagg=sum(PropTaxIncome);
taxtoincome=Cagg/Propertaxagg;
TaxbyInc=sum(PropTaxIncome)/sum(sum(WageInd.*inw, 2)./sum(inw, 2)); %redo this
%TaxbyInc=sum(PropTaxIncome)/sum(sum(WageInd, 2)/500);
%TaxbyInc=sum(PropTaxIncome)/sum(sum(WageInd.*worker, 2)/500);
%Commuting Cost

%Housing size
HresMinbyHres=HresMin/mean(mean(HresInd(:,:),2));
HresMin=NormSqft*HresMin; 
% fracbeqannByYear=NewBornByYear.*BequestByYear./NetWealthByYear;



nf(1:10,:)=0;
for t=11:T
    in1=LOCind(t,:)==1 & RenterInd(t,:)==2;
    in2=LOCind(t,:)==2 & RenterInd(t,:)==2;
    nf(t,1)=ForDemTot(t,1)*nAgent/mean(HresInd(t,in1));
    nf(t,2)=ForDemTot(t,2)*nAgent/mean(HresInd(t,in2));
end

P1=kron(out(:,10),ones(1,nAgent));
P2=kron(out(:,11),ones(1,nAgent));
Rent1=kron(out(:,3),ones(1,nAgent));
Rent2=kron(out(:,4),ones(1,nAgent));
for t=1:T
    in1=LOCind(t,:)==1; 
    in2=LOCind(t,:)==2; 
    in1mkt=LOCind(t,:)==1 & RenterInd(t,:)<3;
    inown=RenterInd(t,:)==2;
    inrent=RenterInd(t,:)==1;
    in1rc=LOCind(t,:)==1 & RenterInd(t,:)==3;
    in1own=LOCind(t,:)==1 & RenterInd(t,:)==2;
    in1rent=LOCind(t,:)==1 & RenterInd(t,:)==1;
    in2mkt=LOCind(t,:)==2 & RenterInd(t,:)<3;
    in2rc=LOCind(t,:)==2 & RenterInd(t,:)==3;
    in2own=LOCind(t,:)==2 & RenterInd(t,:)==2;
    in2rent=LOCind(t,:)==2 & RenterInd(t,:)==1;
    meanLIPT(t,:)=[mean(LIPTind(t,in1)) mean(LIPTind(t,in2)) mean(LIPTind(t,:))]; 
    meanLI(t,:)=[mean(LIind(t,in1)) mean(LIind(t,in2)) mean(LIind(t,:))]; 
    totLI(t,:)=[sum(LIind(t,in1)) sum(LIind(t,in2))];
    meanHres(t,:)=[mean(HresInd(t,in1)) mean(HresInd(t,in2))];
    totPrice(t,:)=[sum(P1(t,in1mkt).*HresInd(t,in1mkt))+sum(P1(t,in1rc).*HresInd(t,in1rc))*(1-RCrentred(1))+P1(t,1)*nAgent*ForDemTot(t,1) sum(P2(t,in2mkt).*HresInd(t,in2mkt))+sum(P2(t,in2rc).*HresInd(t,in2rc))*(1-RCrentred(2))+P2(t,1)*nAgent*ForDemTot(t,2)];
    meanPriceOwn(t,:)=[mean(P1(t,in1own).*HresInd(t,in1own)) mean(P2(t,in2own).*HresInd(t,in2own))];
    meanSizeOwn(t,:)=[mean(HresInd(t,in1own)) mean(HresInd(t,in2own))];
    P0(t,:)=(P1(t,:).*in1+P2(t,:).*in2).*(1-RCrentred(LOCind(t,:)).*(RenterInd(t,:)==3));
    Rent0(t,:)=Rent1(t,:).*in1+Rent2(t,:).*in2;
    meanValOwn(t,:)=[mean(HresInd(t,in1own).*P1(t,in1own)) mean(HresInd(t,in2own).*P2(t,in2own)) mean(HresInd(t,inown).*P0(t,inown))];
    meanRent(t,:)=[mean(HresInd(t,in1rent).*Rent1(t,in1rent)) mean(HresInd(t,in2rent).*Rent2(t,in2rent)) mean(HresInd(t,inrent).*Rent0(t,inrent))];
    Hres(t,:)=[sum(HresInd(t,in1)) sum(HresInd(t,in2))];
    HresOwner(t,:)=[sum(HresInd(t,in1own)) sum(HresInd(t,in2own))];
end

ConsExpInd=zeros(T,nAgent);
for t=1:T-1
    for i=1:nAgent
        td=0;
        if AgeInd(t+1,i)>1
            for j=1:min(nAge-1,T-t)
                if AgeInd(t+j,i)==1 && td==0; td=j-1; end
            end
        end
        ConsExpInd(t,i)=sum((Cind(t:t+td,i)+HexpInd(t:t+td,i)).*(PriceBond.^[0:td]'));
    end
end

%Multiply any model financial quantity by DollarMultiplier to get dollars. 
%If the model quantity is a 4-year cash flow, and if want a 1-year dollar amount, should divide cash flow by 4 to convert to 1 year cash flow
%If model quantity is a per household average, then multiply by NYCpop
%For example, if GovSurp=0.08 (per household per 4 years) then to convert to annual dollars: GovSurp*0.25*DollarMultiplier*NYCpop

% clear Tbl_Rsqr
% for iReg=1:8;
%     for iHF=1:2;
%     for iHFnext=1:2;
%         in=out(:,1)==iHF & outnext(:,1)==iHFnext & [1:T]'>100;
%         y=outnext(in,1+iReg);
%         if iReg<=3; 
%             x=[ones(sum(in),1) out(in,1+iReg) 0.5*(out(in,7)+out(in,8))];
%         else
%             x=[ones(sum(in),1) out(in,1+iReg)];
%         end;
%         if iReg==8;
%             x=[ones(sum(in),1) 0.5*(out(in,3)+out(in,4))];
%         end;
% %        if iReg==1; 
% %            x=[ones(sum(in),1) out(in,1+iReg) .5*(out(in,3)+out(in,4))]; 
% %        else; 
% %            x=[ones(sum(in),1) out(in,2) out(in,1+iReg)]; 
% %        end;
%         b=nwest(y,x,1);
%         Tbl_Rsqr(iReg,(iHF-1)*2+iHFnext)=b.rsqr;
%         Y(in,1:2)=[y x*b.beta];
%     end;
%     end;    
%     Tbl_Rsqr(iReg,5)=1-sum((Y(101:T-1,1)-Y(101:T-1,2)).^2)/sum((Y(101:T-1,1)-mean(Y(101:T-1,1))).^2);
% end;

% disp(Tbl_Rsqr)

%market clearing error
Tbl_MktClr=...
[mean(abs(out(:,12)-out(:,13)))./mean(.5*(out(:,12)+out(:,13))) ...
 mean(abs(out(:,14)+HFVgrid(out(:,1),1).*ForDemTot(:,1)-out(:,7)))./mean(.5*(out(:,14)+HFVgrid(out(:,1),1).*ForDemTot(:,1)+out(:,7))) ...
 mean(abs(out(:,15)+HFVgrid(out(:,1),2).*ForDemTot(:,2)-out(:,8)))./mean(.5*(out(:,15)+HFVgrid(out(:,1),2).*ForDemTot(:,2)+out(:,8))) ...
 mean(abs(out(:,16)-out(:,17)-(1-HFVgrid(out(:,1),1)).*ForDemTot(:,1)))./mean(.5*(out(:,16)+out(:,17)+(1-HFVgrid(out(:,1),1)).*ForDemTot(:,1))) ...
 mean(abs(out(:,18)-out(:,19)-(1-HFVgrid(out(:,1),2)).*ForDemTot(:,2)))./mean(.5*(out(:,18)+out(:,19)+(1-HFVgrid(out(:,1),2)).*ForDemTot(:,2)))];
disp(Tbl_MktClr);

%Tbl_Moments1=...
%[mean(out(in0,2:8)) mean(out(in0,10:11)) mean(out(in0,10:11))./mean(out(in0,3:4)) mean(totPrice(in0,:)./totLI(in0,:));
% mean(out(in1,2:8)) mean(out(in1,10:11)) mean(out(in1,10:11))./mean(out(in1,3:4)) mean(totPrice(in1,:)./totLI(in1,:));
% mean(out(in2,2:8)) mean(out(in2,10:11)) mean(out(in2,10:11))./mean(out(in2,3:4)) mean(totPrice(in2,:)./totLI(in2,:))];
% Tbl_Moments1=...
% [mean(out(in0,2:8)) mean(out(in0,10:11)) mean(out(in0,10:11))./mean(out(in0,3:4)) mean(meanPriceOwn(in0,:)./meanLI(in0,1:2));
%  mean(out(in1,2:8)) mean(out(in1,10:11)) mean(out(in1,10:11))./mean(out(in1,3:4)) mean(meanPriceOwn(in1,:)./meanLI(in1,1:2));
%  mean(out(in2,2:8)) mean(out(in2,10:11)) mean(out(in2,10:11))./mean(out(in2,3:4)) mean(meanPriceOwn(in2,:)./meanLI(in2,1:2))];
in0=[1:T]'>100; in1=[1:T]'>100 & out(:,1)==1; in2=[1:T]'>100 & out(:,1)==2;

Tbl_Moments1=...
[mean(out(in0,2:8)) mean(out(in0,10:11)) mean(out(in0,10:11))./mean(out(in0,3:4)) mean(meanSizeOwn(in0,:)).*mean([P1(in0) P2(in0)]./meanLI(in0,1:2));
 mean(out(in1,2:8)) mean(out(in1,10:11)) mean(out(in1,10:11))./mean(out(in1,3:4)) mean(meanSizeOwn(in0,:)).*mean([P1(in1) P2(in1)]./meanLI(in1,1:2));
 mean(out(in2,2:8)) mean(out(in2,10:11)) mean(out(in2,10:11))./mean(out(in2,3:4)) mean(meanSizeOwn(in0,:)).*mean([P1(in2) P2(in2)]./meanLI(in2,1:2))];

for t=1:T
    inL1=LOCind(t,:)==1;
    inL2=LOCind(t,:)==2; 
    inL3=LOCind(t,:)==3;
    zoneNum(t,1:3)=[sum(inL1) sum(inL2) sum(inL3)];
    zoneAge(t,:)=[mean(AgeInd(t,inL1)) mean(AgeInd(t,inL2))];
    zoneHours(t,:)=[mean(HoursInd(t,inL1)) mean(HoursInd(t,inL2))];
    zoneProd(t,:)=[mean(Zind(t,inL1)) mean(Zind(t,inL2))];
    zoneWealth(t,:)=[mean(NWind(t,inL1)) mean(NWind(t,inL2))];
    zoneIncome(t,:)=[mean(LIind(t,inL1)) mean(LIind(t,inL2))];
    zoneOwners(t,1:2)=[sum(RenterInd(t,inL1)==2) sum(RenterInd(t,inL2)==2)];
    zoneRC(t,1:2)=[sum(RenterInd(t,inL1)==3)/sum(RenterInd(t,inL1)~=2) sum(RenterInd(t,inL2)==3)/sum(RenterInd(t,inL2)~=2)]; 
    for i=1:nAge
        in=LOCind(t,:)==1 & AgeInd(t,:)==i; 
        zoneNum(t,3+(i-1)*3+1)=sum(in);
        zoneOwners(t,3+(i-1)*3+1)=sum(RenterInd(t,in)==2);
        in=LOCind(t,:)==2 & AgeInd(t,:)==i; 
        zoneOwners(t,3+(i-1)*3+2)=sum(RenterInd(t,in)==2);
        zoneNum(t,3+(i-1)*3+2)=sum(in);
        in=LOCind(t,:)==3 & AgeInd(t,:)==i; 
        zoneOwners(t,3+(i-1)*3+3)=sum(RenterInd(t,in)==2);
        zoneNum(t,3+(i-1)*3+3)=sum(in);
    end
end

% Tbl_Moments2=...
% [mean(zoneNum(in0,1:2))/mean(zoneNum(in0,1)+zoneNum(in0,2)) ... %fraction of population
%  mean(out(in0,7:8)-ForDemTot(in0,1:2)).*nAgent./mean(zoneNum(in0,1:2)) ...                 %dwelling size
%  ... %mean(zoneNum(in0,1:2))./[H1bar H2bar] ...                      %density: people / land
%  ... %mean(out(in0,7:8))./[H1bar H2bar] ...                          %density: built area / land
%  mean(zoneAge(in0,:)) ...                                       %average age
%  mean(zoneProd(in0,:)) ...                                      %productivity relative to age group
%  mean(zoneHours(in0,:)) ...                                     %Hours
%  mean(zoneIncome(in0,:)) ...                                     %income
%  mean(zoneWealth(in0,:)) ...                                    %Wealth
%  mean(zoneOwners(in0,1:2)+nf(in0,1:2))./mean(zoneNum(in0,1:2)+nf(in0,1:2)) ...          %Ownership
%  mean(zoneRC(in0,1:2));                                         %fraction RC relative to all renters
%  mean(zoneNum(in1,1:2))/mean(zoneNum(in1,1)+zoneNum(in1,2)) ... %fraction of population
%  mean(out(in1,7:8)-ForDemTot(in1,1:2)).*nAgent./mean(zoneNum(in1,1:2)) ...                 %dwelling size
%  ... %mean(zoneNum(in1,1:2))./[H1bar H2bar] ...                      %density: people / land
%  ... %mean(out(in1,7:8))./[H1bar H2bar] ...                          %density: built area / land
%  mean(zoneAge(in1,:)) ...                                       %average age
%  mean(zoneProd(in1,:)) ...                                      %productivity relative to age group
%  mean(zoneHours(in1,:)) ...                                     %Hours
%  mean(zoneIncome(in1,:)) ...                                     %income
%  mean(zoneWealth(in1,:)) ...                                    %Wealth
%  mean(zoneOwners(in1,1:2)+nf(in1,1:2))./mean(zoneNum(in1,1:2)+nf(in1,1:2)) ...          %Ownership
%  mean(zoneRC(in1,1:2));                                         %fraction RC relative to all renters
%  mean(zoneNum(in2,1:2))/mean(zoneNum(in2,1)+zoneNum(in2,2)) ... %fraction of population
%  mean(out(in2,7:8)-ForDemTot(in2,1:2)).*nAgent./mean(zoneNum(in2,1:2)) ...                 %dwelling size
%  ... %mean(zoneNum(in2,1:2))./[H1bar H2bar] ...                      %density: people / land
%  ... %mean(out(in2,7:8))./[H1bar H2bar] ...                          %density: built area / land
%  mean(zoneAge(in2,:)) ...                                       %average age
%  mean(zoneProd(in2,:)) ...                                      %productivity relative to age group
%  mean(zoneHours(in2,:)) ...                                     %Hours
%  mean(zoneIncome(in2,:)) ...                                     %income
%  mean(zoneWealth(in2,:)) ...                                    %Wealth
%  mean(zoneOwners(in2,1:2)+nf(in2,1:2))./mean(zoneNum(in2,1:2)+nf(in2,1:2)) ...          %Ownership
%  mean(zoneRC(in2,1:2));                                         %fraction RC relative to all renters
% ];
% 
% 



%            People1/Land1 People2/Land2 Buildings1/Land1 Buildings2/Land2
% Tbl_Density=[mean(zoneNum(in0,1:2)./[H1bar(in0) H2bar(in0)]) mean(out(in0,7:8)./[H1bar(in0) H2bar(in0)]);  
%              mean(zoneNum(in1,1:2)./[H1bar(in1) H2bar(in1)]) mean(out(in1,7:8)./[H1bar(in1) H2bar(in1)]);
%              mean(zoneNum(in2,1:2)./[H1bar(in2) H2bar(in2)]) mean(out(in2,7:8)./[H1bar(in2) H2bar(in2)])];



% disp(Tbl_Moments1);
% disp(Tbl_Moments2);
%Welfare Calculation
dW=zeros(nAge,2); dW1=zeros(nAge,2); dWcount=zeros(nAge,2); dW1weight=zeros(nAge,2); Welfare=zeros(nAge,2);
dWrenter=zeros(nAge,2); dW1renter=zeros(nAge,2); dWrentercount=zeros(nAge,2); dW1renterweight=zeros(nAge,2); 
dWowner=zeros(nAge,2); dW1owner=zeros(nAge,2); dWownercount=zeros(nAge,2); dW1ownerweight=zeros(nAge,2); 
dWinc1=zeros(nAge,2); dWinc1count=zeros(nAge,2); dWinc2=zeros(nAge,2); dWinc2count=zeros(nAge,2); dWinc3=zeros(nAge,2); dWinc3count=zeros(nAge,2);
dWnw1=zeros(nAge,2); dWnw1count=zeros(nAge,2); dWnw2=zeros(nAge,2); dWnw2count=zeros(nAge,2); dWnw3=zeros(nAge,2); dWnw3count=zeros(nAge,2);
for t=101:T
    for i=1:nAge
        in=AgeInd(t,:)==i & WelfInd(t,:)>-100000000 & WelfIndAlt(t,:)>-100000000;
        dW(i,out(t,1))=dW(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
        Welfare(i,out(t,1))=Welfare(i,out(t,1))+sum(WelfInd(t,in));%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
        dW1(i,out(t,1))=dW1(i,out(t,1))+sum((-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0).*ConsExpInd(t,in));
        dWcount(i,out(t,1))=dWcount(i,out(t,1))+sum(in);
        dW1weight(i,out(t,1))=dW1weight(i,out(t,1))+sum(ConsExpInd(t,in));
        in=AgeInd(t,:)==i & (RenterIndLast(t,:)==1 | RenterIndLast(t,:)==3) & WelfInd(t,:)>-100000000 & WelfIndAlt(t,:)>-100000000;
        dWrenter(i,out(t,1))=dWrenter(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
        dW1renter(i,out(t,1))=dW1renter(i,out(t,1))+sum((-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0).*ConsExpInd(t,in));
        dWrentercount(i,out(t,1))=dWrentercount(i,out(t,1))+sum(in);
        dW1renterweight(i,out(t,1))=dW1renterweight(i,out(t,1))+sum(ConsExpInd(t,in));
        in=AgeInd(t,:)==i & RenterIndLast(t,:)==2 & WelfInd(t,:)>-100000000 & WelfIndAlt(t,:)>-100000000;
        dWowner(i,out(t,1))=dWowner(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
        dW1owner(i,out(t,1))=dW1owner(i,out(t,1))+sum((-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0).*ConsExpInd(t,in));
        dWownercount(i,out(t,1))=dWownercount(i,out(t,1))+sum(in);
        dW1ownerweight(i,out(t,1))=dW1ownerweight(i,out(t,1))+sum(ConsExpInd(t,in));
        in0=AgeInd(t,:)==i;
        e1=.001*randn(1,nAgent); 
        s=LIind(t,in0)+e1(in0); s=sort(s);
        if sum(in0)>=3
         in=AgeInd(t,:)==i & LIind(t,:)+e1<=s(round(.25*sum(in0)));
         dWinc1(i,out(t,1))=dWinc1(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
         dWinc1count(i,out(t,1))=dWinc1count(i,out(t,1))+sum(in);
         in=AgeInd(t,:)==i & ( LIind(t,:)+e1>s(round(.25*sum(in0))) & LIind(t,:)+e1<s(round(.75*sum(in0))) | (i==20 & LIind(t,:)+e1>=s(round(.25*sum(in0))) & LIind(t,:)+e1<=s(round(.75*sum(in0)))) );
         dWinc2(i,out(t,1))=dWinc2(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
         dWinc2count(i,out(t,1))=dWinc2count(i,out(t,1))+sum(in);
         in=AgeInd(t,:)==i & LIind(t,:)+e1>=s(round(.75*sum(in0)));
         dWinc3(i,out(t,1))=dWinc3(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
         dWinc3count(i,out(t,1))=dWinc3count(i,out(t,1))+sum(in);
        end
        e1=.001*randn(1,nAgent); 
        s=NWind(t,in0)+e1(in0); s=sort(s);
        if sum(in0)>=3
         in=AgeInd(t,:)==i & NWind(t,:)+e1<=s(round(.25*sum(in0)));
         dWnw1(i,out(t,1))=dWnw1(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
         dWnw1count(i,out(t,1))=dWnw1count(i,out(t,1))+sum(in);
         in=AgeInd(t,:)==i & ( NWind(t,:)+e1>s(round(.25*sum(in0))) & NWind(t,:)+e1<s(round(.75*sum(in0))) | (i==20 & NWind(t,:)+e1>=s(round(.25*sum(in0))) & NWind(t,:)+e1<=s(round(.75*sum(in0)))) );
         dWnw2(i,out(t,1))=dWnw2(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
         dWnw2count(i,out(t,1))=dWnw2count(i,out(t,1))+sum(in);
         in=AgeInd(t,:)==i & NWind(t,:)+e1>=s(round(.75*sum(in0)));
         dWnw3(i,out(t,1))=dWnw3(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
         dWnw3count(i,out(t,1))=dWnw3count(i,out(t,1))+sum(in);
        end
    end
end

% dWprod=zeros(6,2); dWprodcount=zeros(6,2);
% dWprodrenter=zeros(6,2); dWprodrentercount=zeros(6,2);
% dWprodowner=zeros(6,2);dWprodownercount=zeros(6,2);
% 
% for t=101:T
%     for i=1:6
%         in=iZind(t,:)==i;
%         dWprod(i,out(t,1))=dWprod(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
%         dWprodcount(i,out(t,1))=dWprodcount(i,out(t,1))+sum(in);
%         in=iZind(t,:)==i & (RenterIndLast(t,:)==1 | RenterIndLast(t,:)==3);
%         dWprodrenter(i,out(t,1))=dWprodrenter(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
%         dWprodrentercount(i,out(t,1))=dWprodrentercount(i,out(t,1))+sum(in);
%         in=iZind(t,:)==i & RenterIndLast(t,:)==2;
%         dWprodowner(i,out(t,1))=dWprodowner(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
%         dWprodownercount(i,out(t,1))=dWprodownercount(i,out(t,1))+sum(in);
%     end
% end
% 
% dWprod=dWprod./dWprodcount; in=dWprodcount==0; dWprod(in)=0; 
% dWprodrenter=dWprodrenter./dWprodrentercount;  in=dWprodrentercount==0; dWprodrenter(in)=0;
% dWprodowner=dWprodowner./dWprodownercount;  in=dWprodownercount==0; dWprodowner(in)=0;
% 
dWprod=zeros(3,2); dWprodcount=zeros(3,2);
dWprodrenter=zeros(3,2); dWprodrentercount=zeros(3,2);
dWprodowner=zeros(3,2);dWprodownercount=zeros(3,2);

for t=101:T
    for i=1:3
        in=(iZind(t,:)==i | iZind(t,:)==i+3);
        dWprod(i,out(t,1))=dWprod(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);
        dWprodcount(i,out(t,1))=dWprodcount(i,out(t,1))+sum(in);
        in=(iZind(t,:)==i | iZind(t,:)==i+3) & (RenterIndLast(t,:)==1 | RenterIndLast(t,:)==3);
        dWprodrenter(i,out(t,1))=dWprodrenter(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
        dWprodrentercount(i,out(t,1))=dWprodrentercount(i,out(t,1))+sum(in);
        in=(iZind(t,:)==i | iZind(t,:)==i+3) & RenterIndLast(t,:)==2;
        dWprodowner(i,out(t,1))=dWprodowner(i,out(t,1))+sum(-1+(WelfIndAlt(t,in)./WelfInd(t,in)).^exp0);%mean(WelfIndAlt(t,in)-WelfInd(t,in))/mean(-WelfInd(t,in));
        dWprodownercount(i,out(t,1))=dWprodownercount(i,out(t,1))+sum(in);
    end
end

dWprod=dWprod./dWprodcount; in=dWprodcount==0; dWprod(in)=0; 
dWprodrenter=dWprodrenter./dWprodrentercount;  in=dWprodrentercount==0; dWprodrenter(in)=0;
dWprodowner=dWprodowner./dWprodownercount;  in=dWprodownercount==0; dWprodowner(in)=0;




%Note that this uses RenterIndLast to identify an owner. Thus if household
%i died at t-1 and was an owner, then household i at t is not considered an
%owner. For this reason actual ownership rate is higher than what would be
%implied by RenterIndLast, the difference being the number of dead owners.
%Thus, x*dWown+(1-x)*dWrenter=dWall holds for x being the ownership rate
%implied by RenterIndLast (that is excluding dead owners), not by the
%actual ownership rate
dW=dW./dWcount; in=dWcount==0; dW(in)=0; dW(nAge+1,:)=sum(dW(1:nAge,:).*dWcount(1:nAge,:))./sum(dWcount(1:nAge,:)); 
Welfare=sum(Welfare(:,1))/sum(dWcount(:,1));
%dW1=dW1./dWcount;  in=dWcount==0; dW1(in)=0; dW1(nAge+1,:)=sum(dW1(1:nAge,:).*dWcount(1:nAge,:))./sum(dWcount(1:nAge,:));
dW1=dW1./dW1weight;  in=dWcount==0; dW1(in)=0; dW1(nAge+1,:)=sum(dW1.*dW1weight)./sum(dW1weight);
dWrenter=dWrenter./dWrentercount;  in=dWrentercount==0; dWrenter(in)=0; dWrenter(nAge+1,:)=sum(dWrenter(1:nAge,:).*dWrentercount(1:nAge,:))./sum(dWrentercount(1:nAge,:)); 
%dW1renter=dW1renter./dWrentercount;  in=dWrentercount==0; dW1renter(in)=0; dW1renter(nAge+1,:)=sum(dW1renter(1:nAge,:).*dWrentercount(1:nAge,:))./sum(dWrentercount(1:nAge,:));
dW1renter=dW1renter./dW1renterweight;  in=dWrentercount==0; dW1renter(in)=0; dW1renter(nAge+1,:)=sum(dW1renter.*dW1renterweight)./sum(dW1renterweight);
dWowner=dWowner./dWownercount;  in=dWownercount==0; dWowner(in)=0; dWowner(nAge+1,:)=sum(dWowner(1:nAge,:).*dWownercount(1:nAge,:))./sum(dWownercount(1:nAge,:)); 
%dW1owner=dW1owner./dWownercount; in=dWownercount==0; dW1owner(in)=0; dW1owner(nAge+1,:)=sum(dW1owner(1:nAge,:).*dWownercount(1:nAge,:))./sum(dWownercount(1:nAge,:));
dW1owner=dW1owner./dWownercount; in=dWownercount==0; dW1owner(in)=0; dW1owner(nAge+1,:)=sum(dW1owner.*dW1ownerweight)./sum(dW1ownerweight);
dWinc1=dWinc1./dWinc1count; dWinc2=dWinc2./dWinc2count; dWinc3=dWinc3./dWinc3count; 
dWnw1=dWnw1./dWnw1count; dWnw2=dWnw2./dWnw2count; dWnw3=dWnw3./dWnw3count; 

Tbl_dW=[dW dWrenter dWowner];
Tbl_dWinc=[dWinc1 dWinc2 dWinc3];
Tbl_dWnw=[dWnw1 dWnw2 dWnw3];

Tbl_dW1=[dW1 dW1renter dW1owner];

disp(Tbl_dW);
disp(Tbl_dW1);

%Wage Rent1 Rent2 P1 P2 RP1 RP2 P1/Rent1 P2/Rent2 P1/Inc1 P2/Inc2
Tbl_Moments1out=[Tbl_Moments1(:,[1:3 8:9 4:5]) 4*Tbl_Moments1(:,10:13)];
%fprintf('Average      & %5.3f & %5.4f & %5.4f & %5.3f & %5.3f & %6.4f & %6.4f & %5.3f & %5.3f & %5.3f & %5.3f \\\\ \n',Tbl_Moments1out(1,:))
%fprintf('Low Foreign  & %5.3f & %5.4f & %5.4f & %5.3f & %5.3f & %6.4f & %6.4f & %5.3f & %5.3f & %5.3f & %5.3f \\\\ \n',Tbl_Moments1out(2,:))
%fprintf('High Foreign & %5.3f & %5.4f & %5.4f & %5.3f & %5.3f & %6.4f & %6.4f & %5.3f & %5.3f & %5.3f & %5.3f \\\\ \n',Tbl_Moments1out(3,:))

%pop1 Structures1 Structures2 DeltaHouseSize DeltaDensity DeltaAge DeltaIncome DeltaNetWorth Own1 Own2
% Tbl_Moments2out=[Tbl_Moments2(:,1) Tbl_Moments1(:,6) Tbl_Moments1(:,7) Tbl_Moments2(:,3)./Tbl_Moments2(:,4) Tbl_Density(:,1)./Tbl_Density(:,2) (Tbl_Moments2(:,5)*4+20)./(Tbl_Moments2(:,6)*4+20) Tbl_Moments2(:,11)./Tbl_Moments2(:,12) Tbl_Moments2(:,13)./Tbl_Moments2(:,14) Tbl_Moments2(:,15) Tbl_Moments2(:,16)];
%fprintf('Average      & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f \\\\ \n',Tbl_Moments2out(1,:))
%fprintf('Low Foreign  & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f \\\\ \n',Tbl_Moments2out(2,:))
%fprintf('High Foreign & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f & %5.3f \\\\ \n',Tbl_Moments2out(3,:))

%NYC P/R use price per square foot divided by rent per square foot
%VAN P/R use average value of owner's house divided by average rent of renter's house: 4*mean(meanValOwn(in0,:)./meanRent(in0,:))
in0=[1:T]'>100; in1=[1:T]'>100 & out(:,1)==1; in2=[1:T]'>100 & out(:,1)==2;
Area=77.989; LandSh1=2.38; Pop=7.1249; AvgInc=97.577; %NYC
% Tbl_NYCmoments=[
%  Area LandSh1
%  Pop 100*Tbl_Moments2out(1,1)/(1-Tbl_Moments2out(1,1)) 
%  100*mean(zoneOwners(:,1)+zoneOwners(:,2)+nf(:,1)+nf(:,2))/mean(zoneNum(:,1)+zoneNum(:,2)+nf(:,1)+nf(:,2)) (mean(zoneOwners(:,1)+nf(:,1))/mean(zoneNum(:,1)+nf(:,1)))/(mean(zoneOwners(:,2)+nf(:,2))/mean(zoneNum(:,2)+nf(:,2)))
%  AvgInc Tbl_Moments2out(1,7)
%  100*sum(sum(RenterInd==3))/sum(sum(RenterInd==1 | RenterInd==3)) (sum(sum(RenterInd==3 & LOCind==1))/sum(sum((RenterInd==1 | RenterInd==3) & LOCind==1)))/(sum(sum(RenterInd==3 & LOCind==2))/sum(sum((RenterInd==1 | RenterInd==3) & LOCind==2)))
%  100*sum(sum(AgeInd>11))/sum(sum(AgeInd>0)) (sum(sum(AgeInd>11 & LOCind==1))/sum(sum(AgeInd>0 & LOCind==1)))/(sum(sum(AgeInd>11 & LOCind==2))/sum(sum(AgeInd>0 & LOCind==2)))
%  AvgInc*4*mean(meanValOwn(in0,3))./mean(meanLIPT(in0,3)) mean(meanValOwn(in0,1))/mean(meanValOwn(in0,2))
%  AvgInc*mean(meanRent(in0,3))./mean(meanLIPT(in0,3)) mean(out(in0,3))/mean(out(in0,4))
%  4*((mean(out(in0,10))./mean(out(in0,3)))*mean(out(in0,7))+(mean(out(in0,11))./mean(out(in0,4)))*mean(out(in0,8)))/(mean(out(in0,7)+mean(out(in0,8)))) Tbl_Moments1out(1,8)/Tbl_Moments1out(1,9)
%  4*mean(meanValOwn(in0,3))./mean(meanLIPT(in0,3)) (mean(meanValOwn(in0,1))./mean(meanLIPT(in0,1)))/(mean(meanValOwn(in0,2))./mean(meanLIPT(in0,2)))
%  100*mean(meanRent(in0,3)./meanLIPT(in0,3)) (mean(meanRent(in0,1)./meanLIPT(in0,1)))/(mean(meanRent(in0,2)./meanLIPT(in0,2)))
%  mean(mean(AgeInd))*4+20 (mean(mean(AgeInd & LOCind==1))*4+20)/(mean(mean(AgeInd & LOCind==2))*4+20)
%  ];
% Area=2.011; LandSh1=6.1; Pop=0.88645; AvgInc=97.878; %VAN
% Tbl_VANmoments=[
%  Area LandSh1
%  Pop 100*Tbl_Moments2out(1,1)/(1-Tbl_Moments2out(1,1)) 
%  100*mean(zoneOwners(:,1)+zoneOwners(:,2)+nf(:,1)+nf(:,2))/mean(zoneNum(:,1)+zoneNum(:,2)+nf(:,1)+nf(:,2)) (mean(zoneOwners(:,1)+nf(:,1))/mean(zoneNum(:,1)+nf(:,1)))/(mean(zoneOwners(:,2)+nf(:,2))/mean(zoneNum(:,2)+nf(:,2)))
%  AvgInc Tbl_Moments2out(1,7)
%  100*sum(sum(RenterInd==3))/sum(sum(RenterInd==1 | RenterInd==3)) (sum(sum(RenterInd==3 & LOCind==1))/sum(sum((RenterInd==1 | RenterInd==3) & LOCind==1)))/(sum(sum(RenterInd==3 & LOCind==2))/sum(sum((RenterInd==1 | RenterInd==3) & LOCind==2)))
%  100*sum(sum(AgeInd>11))/sum(sum(AgeInd>0)) (sum(sum(AgeInd>11 & LOCind==1))/sum(sum(AgeInd>0 & LOCind==1)))/(sum(sum(AgeInd>11 & LOCind==2))/sum(sum(AgeInd>0 & LOCind==2)))
%  AvgInc*4*mean(meanValOwn(in0,3))./mean(meanLIPT(in0,3)) mean(meanValOwn(in0,1))/mean(meanValOwn(in0,2))
%  AvgInc*mean(meanRent(in0,3))./mean(meanLIPT(in0,3)) mean(out(in0,3))/mean(out(in0,4))
%  4*mean(meanValOwn(in0,3)./meanRent(in0,3)) (mean(meanValOwn(in0,1)./meanRent(in0,1)))/(mean(meanValOwn(in0,2)./meanRent(in0,2)))
%  4*mean(meanValOwn(in0,3))./mean(meanLIPT(in0,3)) (mean(meanValOwn(in0,1))./mean(meanLIPT(in0,1)))/(mean(meanValOwn(in0,2))./mean(meanLIPT(in0,2)))
%  100*mean(meanRent(in0,3)./meanLIPT(in0,3)) (mean(meanRent(in0,1)./meanLIPT(in0,1)))/(mean(meanRent(in0,2)./meanLIPT(in0,2)))
%  mean(mean(AgeInd))*4+20 (mean(mean(AgeInd & LOCind==1))*4+20)/(mean(mean(AgeInd & LOCind==2))*4+20)
%  ];

% for i=1:nAge+1;
%     fprintf('%4i & %8.2f & %8.2f & %8.2f & %8.2f & %8.2f & %8.2f \\\\ \n',[(i-1)*4+21 Tbl_dW(i,:)*100])
% end;

%for i=1:nAge+1;
%    fprintf('%4i & %8.2f & %8.2f & %8.2f \\\\ \n',[(i-1)*4+21 Tbl_dW(i,[5 3 1])*100])
%end;


% %%%%% LIHTC and Vouchers %%%%%%
% Time=kron([1:T]',ones(1,500));
% 
% GovSurpAvg=mean(HSVtaxInd(Time>100));
% 
% HrentTot1=sum(HresInd(LOCind==1 & RenterInd==1 & Time>100))/(nAgent*(T-100));
% HRCTot1=sum(HresInd(LOCind==1 & RenterInd==3 & Time>100))/(nAgent*(T-100));
% Htot1=sum(HresInd(LOCind==1 & Time>100))/(nAgent*(T-100));
% HrentTot2=sum(HresInd(LOCind==2 & RenterInd==1 & Time>100))/(nAgent*(T-100));
% HRCTot2=sum(HresInd(LOCind==2 & RenterInd==3 & Time>100))/(nAgent*(T-100));
% Htot2=sum(HresInd(LOCind==2 & Time>100))/(nAgent*(T-100));
% RentShareOfAll1=((HrentTot1+HRCTot1)/Htot1);
% RentShareOfAll2=((HrentTot2+HRCTot2)/Htot2);
% Subs1=mean(PH1(101:T))*RentShareOfAll1*RCshare(1,1)*(1-RCrentred(1,1))*RCsubs(1,1)*Htot1*deprH(1);
% Subs2=mean(PH2(101:T))*RentShareOfAll2*RCshare(2,1)*(1-RCrentred(2,1))*RCsubs(2,1)*Htot2*deprH(2);
% Subs=Subs1+Subs2; %this is the total LIHTC subsidy scaled by number of households
% RCshareSubs = Subs/(mean(WageBillLOC1(101:T))*RentShareOfAll1*RCshare(1,1)+mean(WageBillLOC2(101:T))*RentShareOfAll2*RCshare(2,1)); %this is the subsidy as a fraction of total RC construction expenses
% SubsDollarCost=Subs*0.25*NYCpop*DollarMultiplier/1000000;
% 
% in=HSVtaxInd<0 & HSVtaxInd<HSVtaxBaseInd;
% VoucherExpenseInd=zeros(T,nAgent);
% VoucherExpenseInd(in)=HSVtaxBaseInd(in)-HSVtaxInd(in);
% VoucherExpenseAvg=mean(VoucherExpenseInd(Time>100)); %per person cost of voucher policy
% VoucherDollarCost=VoucherExpenseAvg*0.25*NYCpop*DollarMultiplier/1000000;
% 
% for t=1:T;
%  RCcostInd(t,:)=(RenterInd(t,:)==3).*RentInd(t,:).*RCrentred(LOCind(t,:),out(t,1))';
% end;
% RCcostAvg=mean(RCcostInd(Time>100)); %per person cost of RC
% RCdollarcost=RCcostAvg*0.25*NYCpop*DollarMultiplier/1000000;
% 

%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%% Figure 2: plot income, wealth, ownership by age and income group %%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

wg_by_age_income=zeros(nAge,5);
nw_by_age_income=zeros(nAge,5);
own_by_age_income=zeros(nAge,5);
for i=1:nAge
    in=AgeInd==i & kron([1:T]',ones(1,nAgent))>100; 
    n=sum(sum(in)); 
%    cut25a=floor(n*.25); cut25b=ceil(n*.25); if cut25b>cut25a; cut25m=(n*.25-cut25a)/(cut25b-cut25a); else; cut25m=0; end;
%    cut50a=floor(n*.50); cut50b=ceil(n*.50); if cut50b>cut50a; cut50m=(n*.50-cut50a)/(cut50b-cut50a); else; cut50m=0; end;
%    cut75a=floor(n*.75); cut75b=ceil(n*.75); if cut75b>cut75a; cut75m=(n*.75-cut75a)/(cut75b-cut75a); else; cut75m=0; end;
    cut25a=floor(n*.25); cut25b=ceil(n*.25); if cut25b>cut25a; cut25m=(n*.25-cut25a)/(cut25b-cut25a); else; cut25m=0; end;
    cut75a=min(n,1+ceil(n*.75)); cut75b=min(n,1+floor(n*.75)); %if cut75b>cut75a; cut75m=(n*.75-cut75a)/(cut75b-cut75a); else; cut75m=0; end;
    z=LIPTind(in); nw=NWind(in); own=RenterInd(in);
    if i<=nAge-nRet; wg=WageInd(in); else; wg=LIind(in); end;
    %nw=sort(NWind(t,in));
    [z in0]=sort(z); nw=nw(in0); wg=wg(in0); own=own(in0);
    if n>3
     in25a=[1:n]'<=cut25a; in25b=[1:n]'<=cut25b;
     in50a=[1:n]'>cut25a & [1:n]'<cut75a; in50b=[1:n]'>cut25b & [1:n]'<cut75b; 
     in75a=[1:n]'>=cut75a; in75b=[1:n]'>=cut75b;
     %x(i,:)=x(i,:)+[n mean(nw) nw(cut25a)+cut25m*(nw(cut25b)-nw(cut25a)) nw(cut50a)+cut50m*(nw(cut50b)-nw(cut50a)) nw(cut75a)+cut75m*(nw(cut75b)-nw(cut75a)) sum(RenterIndLast(t+1,in)==2)/sum(in)]; 
     
     wg1=mean(wg(in25a))+cut25m*(mean(wg(in25b))-mean(wg(in25a)));
     wg2=mean(wg(in50a))+cut25m*(mean(wg(in50b))-mean(wg(in50a)));
     wg3=mean(wg(in75a))+cut25m*(mean(wg(in75b))-mean(wg(in75a)));
     wg_by_age_income(i,:)=[n mean(wg) wg1 wg2 wg3];
     
     nw1=mean(nw(in25a))+cut25m*(mean(nw(in25b))-mean(nw(in25a)));
     nw2=mean(nw(in50a))+cut25m*(mean(nw(in50b))-mean(nw(in50a)));
     nw3=mean(nw(in75a))+cut25m*(mean(nw(in75b))-mean(nw(in75a)));
     nw_by_age_income(i,:)=[n mean(nw) nw1 nw2 nw3]; 
     
     own1=(sum(own(in25a)==2)/sum(in25a))+cut25m*((sum(own(in25b)==2)/sum(in25b))-(sum(own(in25a)==2)/sum(in25a)));
     own2=(sum(own(in50a)==2)/sum(in50a))+cut25m*((sum(own(in50b)==2)/sum(in50b))-(sum(own(in50a)==2)/sum(in50a)));
     own3=(sum(own(in75a)==2)/sum(in75a))+cut25m*((sum(own(in75b)==2)/sum(in75b))-(sum(own(in75a)==2)/sum(in75a)));
     own_by_age_income(i,:)=[n sum(own==2)/n own1 own2 own3];
    else;
     if n>0;
      wg_by_age_income(i,:)=[n mean(wg) wg(1) wg(ceil(.5*n)) wg(n)];   
      nw_by_age_income(i,:)=[n mean(nw) nw(1) nw(ceil(.5*n)) nw(n)];
      own_by_age_income(i,:)=[n sum(own==2)/sum(in) own(1)==1 own(ceil(.5*n))==1 own(n)==1];
     end;
    end;
end;
wg_by_age_income(:,1)=wg_by_age_income(:,1)/(T-1-100);
nw_by_age_income(:,1)=nw_by_age_income(:,1)/(T-1-100);
own_by_age_income(:,1)=own_by_age_income(:,1)/(T-1-100);
disp(wg_by_age_income)
disp(nw_by_age_income)
disp(own_by_age_income)
nwmean=(sum(nw_by_age_income(:,1).*nw_by_age_income(:,2))/sum(nw_by_age_income(:,1)));
wgmean=(sum(wg_by_age_income(:,1).*wg_by_age_income(:,2))/sum(wg_by_age_income(:,1)));

%AvgIncomeDollars=1; %normalized to 1
HHsize=1.74; %everything (in model and data) normalizes by household size. However, for Stijn's fractions by income groups, need to multiply income by HHsize
AvgIncomeDollars=31.42; %generic city (thousands), this comes from 2010 WageMeanAll in ModelOfCity_Data code and is income normalized by household size, which is 1.74
AvgInitIncomeDollars=14.68; %generic city (thousands)
%AvgIncomeDollars=97.577/HHsize; %NYC (thousands)
%AvgInitIncomeDollars=(14.68/31.42)*AvgIncomeDollars; %NYC (thousands)

%%
if mode==1 && model==1
    path_fig="../Figures/";
    openfig(join([path_fig, "city_fig_wealth_data_model"], ""))
    subplot(3,2,2); hold off
    plot(([1:18]'-1)*4+22.5,HHsize*AvgInitIncomeDollars*wg_by_age_income(1:18,2)/wg_by_age_income(1,2),'k','LineWidth',3); hold on
    plot(([1:18]'-1)*4+22.5,HHsize*AvgInitIncomeDollars*wg_by_age_income(1:18,3)/wg_by_age_income(1,2),'r--','LineWidth',2)
    plot(([1:18]'-1)*4+22.5,HHsize*AvgInitIncomeDollars*wg_by_age_income(1:18,4)/wg_by_age_income(1,2),'b-.','LineWidth',2)
    plot(([1:18]'-1)*4+22.5,HHsize*AvgInitIncomeDollars*wg_by_age_income(1:18,5)/wg_by_age_income(1,2),'g:','LineWidth',2)
    axis([20 90 0 200])
    %legend('Mean','Bottom 25% income','Middle 50% income','Top 25% income')
    ylabel('Labor Income')
    title('Model')
    subplot(3,2,4); hold off
    plot(([1:nAge]'-1)*4+22.5,HHsize*AvgIncomeDollars*nw_by_age_income(:,2)/(.25*wgmean),'k','LineWidth',3); hold on;
    plot(([1:nAge]'-1)*4+22.5,HHsize*AvgIncomeDollars*nw_by_age_income(:,3)/(.25*wgmean),'r--','LineWidth',2); 
    plot(([1:nAge]'-1)*4+22.5,HHsize*AvgIncomeDollars*nw_by_age_income(:,4)/(.25*wgmean),'b-.','LineWidth',2);
    plot(([1:nAge]'-1)*4+22.5,HHsize*AvgIncomeDollars*nw_by_age_income(:,5)/(.25*wgmean),'g:','LineWidth',2);
    axis([20 90 0 1800])
    %legend('Mean','Bottom 25% income','Middle 50% income','Top 25% income')
    ylabel('Net Worth')
    subplot(3,2,6); hold off
    plot(([1:nAge]'-1)*4+22.5,own_by_age_income(:,2),'k','LineWidth',3); hold on
    plot(([1:nAge]'-1)*4+22.5,own_by_age_income(:,3),'r--','LineWidth',2);
    plot(([1:nAge]'-1)*4+22.5,own_by_age_income(:,4),'b-.','LineWidth',2);
    plot(([1:nAge]'-1)*4+22.5,own_by_age_income(:,5),'g:','LineWidth',2);
    axis([20 90 0 1])
    %legend('Mean','Bottom 25% income','Middle 50% income','Top 25% income')
    ylabel('Ownership')
    xlabel('Age')
    saveas(gcf,join([path_fig, "city_fig_wealth_data_model_updated.png"], ""))
    %close
end

%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%% Figure 3: Welfare Effects of Increase in OOT Housing Demand %%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
if mode==1 && model==1
    y1=[dW(1:20,1) dWrenter(1:20,1) dWowner(1:20,1) ]*100;
    y2=[dWinc1(1:20,1) dWinc2(1:20,1) dWinc3(1:20,1) ]*100;
    y3=[dWnw1(1:20,1) dWnw2(1:20,1) dWnw3(1:20,1) ]*100;
    x=categorical(["21-24","25-28","29-32","33-36","37-40","41-44","45-48","49-52","53-56","57-60",...
        "61-64","65-68","69-72","73-76","77-80","81-84","85-88","89-92","93-96","97-100"]);  
    path_fig="../Figures/";
    openfig(join([path_fig, "welfarebyageincomewealth_updated"], ""))
    subplot(3,1,1); hold off
    bar(x,y1,'grouped');
    legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02])
    ylim([-10 5])
    subplot(3,1,2); hold off
    bar(x,y2,'grouped');
    legend('bottom-25%', 'middle-50%', 'top-25%', 'Position',[0.25 0.45 0.02 0.02])
    ylim([-10 5])
    subplot(3,1,3); hold off
    bar(x,y3,'grouped');
    legend('bottom-25%', 'middle-50%', 'top-25%', 'Position',[0.25 0.15 0.02 0.02])
    ylim([-10 5])
    xlabel("age")
    saveas(gcf,join([path_fig, "welfarebyageincomewealth_updated.png"], ""))
end

%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%% output for Table 2 (Sept 11, 2018) %%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
in0=[1:T]'>100;
own=sum(zoneOwners(:,1:2)+nf(:,1:2),2)./sum(zoneNum(:,1:2)+nf(:,1:2),2);
own1=(zoneOwners(:,1)+nf(:,1))./(zoneNum(:,1)+nf(:,1));
own2=(zoneOwners(:,2)+nf(:,2))./(zoneNum(:,2)+nf(:,2));
HORel=(HORel*version+mean(own1(in0))/mean(own2(in0)))/(version+1);
ownnext=[own(2:end,:); own(end,:)];
ownlocal=zoneOwners(:,1:2)./zoneNum(:,1:2);
ownlocalnext=[ownlocal(2:end,:); ownlocal(end,:)];

%Fraction of Population in Zone 1
ZoneOneFrac=zoneNum(:,1)/500;
zoneNumnext=[zoneNum(2:end,:); zoneNum(end,:)];
ZoneOneFracnext=[ZoneOneFrac(2:end,:); ZoneOneFrac(end,:)];
ZoneOneFracnextnext=[ZoneOneFracnext(2:end,:); ZoneOneFracnext(end,:)];
ZoneTwoFrac=zoneNum(:,2)/500;
ZoneTwoFracnext=[ZoneTwoFrac(2:end,:); ZoneTwoFrac(end,:)];
ZoneTwoFracnextnext=[ZoneTwoFracnext(2:end,:); ZoneTwoFracnext(end,:)];
LuxuryFrac=zoneNum(:,3)/500;
LuxuryFracnext=[LuxuryFrac(2:end,:); LuxuryFrac(end,:)];
LuxuryFracnextnext=[LuxuryFracnext(2:end,:); LuxuryFracnext(end,:)];

% GDP=(HoursDemandC+HoursDemandLOC1+HoursDemandLOC2).*Wage+(out(:,30)+out(:,31)+out(:,32))/2000;
% GDPnext=[GDP(2:end,:); GDP(end,:)];
AvgIncome1next=[AvgIncome1(2:end,:); AvgIncome1(end,:)];
AvgIncome2next=[AvgIncome2(2:end,:); AvgIncome2(end,:)];
outnextnext=[outnext(2:end,:); outnext(end,:)];
outbefore=[zeros(1,50); out(1:(T-1),:)];
in=out(:,1)==1 & outnext(:,1)==2 & [1:T]'>100;
reverse_in=out(:,1)==2 & outbefore(:,1)==1 & [1:T]'>101;

x1=(x1*version+[mean([outnext(in,[2 3 4 10 11 39])./out(in,[2 3 4 10 11 39]) ... %Wage Rent1 Rent2 Price1 Price2 Price Luxury
   (outnextnext(in,7)-(1-deprH(1))*outnext(in,7))./(outnext(in,7)-(1-deprH(1))*out(in,7)) ... %Investment H1
   (outnextnext(in,8)-(1-deprH(1))*outnext(in,8))./(outnext(in,8)-(1-deprH(1))*out(in,8)) ... %Investment H2
   (outnextnext(in,40)-(1-deprH(1))*outnext(in,40))./(outnext(in,40)-(1-deprH(1))*out(in,40)) ... %Investment Luxury  
   (outnext(in,10)./outnext(in,3))./(out(in,10)./out(in,3)) ... %P1/R1
   (outnext(in,11)./outnext(in,4))./(out(in,11)./out(in,4)) ... %P2/R2
   (out(in,7).*outnext(in,10)./AvgIncome1next(in))./(out(in,7).*out(in,10)./AvgIncome1(in)) ... %H1*P1/Y
   (out(in,8).*outnext(in,11)./AvgIncome2next(in))./(out(in,8).*out(in,11)./AvgIncome2(in)) ... %H2*P2/Y
   (out(in,7).*outnext(in,3)./AvgIncome1next(in))./(out(in,7).*out(in,3)./AvgIncome1(in)) ... %H1*R1/Y
   (out(in,8).*outnext(in,4)./AvgIncome2next(in))./(out(in,8).*out(in,4)./AvgIncome2(in)) ... %H2*R2/Y
   ownnext(in)./own(in) ... %own
   ZoneOneFracnext(in)./ZoneOneFrac(in) ...% Fraction of Population in Zone 1
   ZoneTwoFracnext(in)./ZoneTwoFrac(in) ...% Fraction of Population in Zone 2
   LuxuryFracnext(in)./LuxuryFrac(in)])-1 ...% Fraction of Population in Zone 2 Luxury   
   Tbl_dW(21,[1 3 5]) ]*100)/(version+1);



%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%% Earnings change by age %%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Earn=zeros(T,nAge-9); Erenter=zeros(T,nAge-9); Eowner=zeros(T,nAge-9); % change in earnings by age group
% 
% for t=101:T
%     for i=1:nAge-9
%         in_age=AgeInd(t,:)==i; 
%         Earn(t,i)=mean(WageInd(t,in_age));
%         in_age_rent=AgeInd(t,:)==i & RenterInd(t,:)==1;
%         Erenter(t,i)=mean(WageInd(t,in_age_rent));
%         in_age_own=AgeInd(t,:)==i & RenterInd(t,:)==2;
%         Eowner(t,i)=mean(WageInd(t,in_age_own));   
%     end
% end
% Earnnext=[Earn(2:end,:);zeros(1,11)];
% Erenternext=[Erenter(2:end,:);zeros(1,11)];
% Eownernext=[Eowner(2:end,:);zeros(1,11)];
% dE=(nanmean(Earnnext(in,:)./Earn(in,:),1)-1)*100;
% dErenter=(nanmean(Erenternext(in,:)./Erenter(in,:),1)-1)*100;
% dEowner=(mean(Eownernext(in,:)./Eowner(in,:),1)-1)*100;

for i=1:nAge
    in_age=AgeInd==i & repmat(in,1,500);
    in_age_next=AgeInd==i & repmat(reverse_in,1,500);
    dE(i,1)=(dE(i,1)*version+(mean(WageInd(in_age_next))/mean(WageInd(in_age))-1)*100)/(version+1);
    in_age_rent=AgeInd==i & RenterInd==1 & repmat(in,1,500);
    in_age_rent_next=AgeInd==i & RenterInd==1 & repmat(reverse_in,1,500);
    dErenter(i,1)=(dErenter(i,1)*version+(mean(WageInd(in_age_rent_next))/mean(WageInd(in_age_rent))-1)*100)/(version+1);
    in_age_own=AgeInd==i & RenterInd==2 & repmat(in,1,500);
    in_age_own_next=AgeInd==i & RenterInd==2 & repmat(reverse_in,1,500);
    dEowner(i,1)=(dEowner(i,1)*version+(mean(WageInd(in_age_own_next))/mean(WageInd(in_age_own))-1)*100)/(version+1);
end

% if mode==1 && (model==1 || model==length(model_space))
%     order=[1,4,2,5,3,6];
%     if version==0
%         yprod=[dWprod(order,1) dWprodrenter(order,1) dWprodowner(order,1) ]*100;
%     else
%         yprod=(yprod*version+[dWprod(order,1) dWprodrenter(order,1) dWprodowner(order,1) ]*100)/(version+1);
%     end
%     x=categorical(["Low & impatient","Low & patient","Med & impatient","Med & patient","High & impatient","High & patient"]);  
%     x=reordercats(x,{'Low & impatient','Low & patient','Med & impatient','Med & patient','High & impatient','High & patient'});
%     path_fig="../Figures/";
%     openfig(join([path_fig, "welfare_by_productivity_baseline_taxtolow"], ""))
%     if model==1
%     subplot(2,1,1); hold off
%     bar(x,yprod,'grouped');
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02])
%     saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow.png"], ""))
%     else
%     subplot(2,1,2); hold off
%     bar(x,yprod,'grouped');
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02])
%     saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow.png"], ""))   
%     end
% end

if mode==1 && (model==1 || model==length(model_space)-1 || model==length(model_space)-2 || model==length(model_space)-3)
    if version==0
        yprod=[dWprod(:,1) dWprodrenter(:,1) dWprodowner(:,1) ]*100;
    else
        yprod=(yprod*version+[dWprod(:,1) dWprodrenter(:,1) dWprodowner(:,1) ]*100)/(version+1);
    end
    x=categorical(["Low","Med","High"]);  
    x=reordercats(x,{'Low','Med','High'});
    path_fig="../Figures/";
    openfig(join([path_fig, "welfare_by_productivity_baseline_taxtolow1"], ""))
    if model==1
    subplot(2,2,1);
    bar(x,yprod,'grouped');
    ylim([-4,6])
    yticks(-4:1:6)
    title({'(a) OOT tax rate = 6.3% + 0%', 'all to public goods'});
    legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02]);
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow1"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow1.png"], ""))
    elseif model==length(model_space)-3
    subplot(2,2,2); 
    bar(x,yprod,'grouped');
    ylim([-4,6])
    yticks(-4:1:6)
    title({'(b) OOT tax rate = 6.3% + 3.46%', 'all to public goods'});
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02]);
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow1"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow1.png"], ""))   
    elseif model==length(model_space)-2
    subplot(2,2,3); 
    bar(x,yprod,'grouped');
    title({'(c) OOT tax rate = 6.3% + 3.46%', 'surcharge to low productivity'})
    ylim([-4,6])
    yticks(-4:1:6)
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02]);
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow1"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow1.png"], ""))   
    else
    subplot(2,2,4); 
    bar(x,yprod,'grouped');
    title({'(d) OOT tax rate = 6.3% + 3.46%', 'all to low productivity'});
    ylim([-4,6])
    yticks(-4:1:6)
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02])
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow1"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow1.png"], ""))   
    end
end

if mode==1 && (model==1 || model==length(model_space)-1 || model==length(model_space)-2 || model==length(model_space)-3)
    if version==0
        yprod=[dWprod(:,1) dWprodrenter(:,1) dWprodowner(:,1) ]*100;
    else
        yprod=(yprod*version+[dWprod(:,1) dWprodrenter(:,1) dWprodowner(:,1) ]*100)/(version+1);
    end
    x=categorical(["Low","Med","High"]);  
    x=reordercats(x,{'Low','Med','High'});
    path_fig="../Figures/";
    openfig(join([path_fig, "welfare_by_productivity_baseline_taxtolow2"], ""))
    if model==1
    subplot(2,2,1);
    bar(x,yprod,'grouped');
    ylim([-4,1])
    yticks(-4:1:1)
    title({'(a) OOT tax rate = 6.3% + 0%', 'all to public goods'});
    legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02]);
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow2"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow2.png"], ""))
    elseif model==length(model_space)-3
    subplot(2,2,2); 
    bar(x,yprod,'grouped');
    ylim([-4,1])
    yticks(-4:1:1)
    title({'(b) OOT tax rate = 6.3% + 3.46%', 'all to public goods'});
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02]);
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow2"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow2.png"], ""))   
    elseif model==length(model_space)-2
    subplot(2,2,3); 
    bar(x,yprod,'grouped');
    title({'(c) OOT tax rate = 6.3% + 3.46%', 'surcharge to low productivity'})
    ylim([-1,6])
    yticks(-1:1:6)
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02]);
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow2"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow2.png"], ""))   
    else
    subplot(2,2,4); 
    bar(x,yprod,'grouped');
    title({'(d) OOT tax rate = 6.3% + 3.46%', 'all to low productivity'});
    ylim([-1,6])
    yticks(-1:1:6)
%     legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02])
    savefig(join([path_fig, "welfare_by_productivity_baseline_taxtolow2"], ""))
    saveas(gcf,join([path_fig, "welfare_by_productivity_baseline_taxtolow2.png"], ""))   
    end
end

% yearnings=[dE(1:11) dErenter(1:11) dEowner(1:11)];
% x=categorical(["21-24", "25-28", "29-32","33-36","37-40","41-44","45-48","49-52","53-56","57-60",...
%     "61-64"]);  
% path_fig="../Figures/";
% openfig(join([path_fig, "Earningsbyage"], ""))
% bar(x,yearnings,'grouped');
% legend('all', 'renter', 'owner', 'Position',[0.25 0.75 0.02 0.02])
% xlabel("age")
% saveas(gcf,join([path_fig, "Earningsbyage.png"], ""))
%short_run=strjoin(arrayfun(@(x) num2str(x),x1,'UniformOutput',false),' & ');

% PYZ1A=mean(out(in,7).*outnext(in,10)./GDPnext(in))*4;
% PYZ1=mean(out(in,7).*out(in,10)./GDP(in))*4;
% PYZ2A=mean(out(in,8).*outnext(in,11)./GDPnext(in))*4;
% PYZ2=mean(out(in,8).*out(in,11)./GDP(in))*4;



% Earnings, Wealth, and Home Ownership
% Ownership Rate 
in_high=out(:,1)==2 & [1:T]'>100;
in_low=out(:,1)==1 & [1:T]'>100;
OwnRate=(OwnRate*version+mean(own(in0))*100)/(version+1);
OwnRateBefore=(OwnRateBefore*version+mean(own(in))*100)/(version+1);
OwnRateAfter=(OwnRateAfter*version+mean(ownnext(in))*100)/(version+1);
% Composition Effect
MidAge1=AgeInd>=7 & AgeInd<= 11 & LOCind==1;
WtMid1=MidAge1./sum(MidAge1,2);
NWindMid1=sum(NWind.*WtMid1,2);
NWindMid1next=[NWindMid1(2:end);NWindMid1(end)];
NWindMid1Ch1=(NWindMid1Ch1*version+(mean(NWindMid1next(in)./NWindMid1(in))-1)*100)/(version+1);
WageIndMid1=sum(WageInd.*WtMid1,2);
WageIndMid1next=[WageIndMid1(2:end);WageIndMid1(end)];
WageIndMid1Ch1=(WageIndMid1Ch1*version+(mean(WageIndMid1next(in)./WageIndMid1(in))-1)*100)/(version+1);
OwnLocalChangeZ1=(OwnLocalChangeZ1*version+(mean(ownlocalnext(in,1)./ownlocal(in,1))-1)*100)/(version+1);
OwnLocalChangeZ2=(OwnLocalChangeZ2*version+(mean(ownlocalnext(in,2)./ownlocal(in,2))-1)*100)/(version+1);
%Labor Market
SizeChShort=(SizeChShort*version+(mean((outnext(in,7).*zoneNumnext(in,1)+outnext(in,8).*zoneNumnext(in,2))./(out(in,7).*zoneNum(in,1)+out(in,8).*zoneNum(in,2)))-1)*100)/(version+1);
SizeChLong=(SizeChLong*version+(mean((out(in2,7).*zoneNum(in2,1)+out(in2,8).*zoneNum(in2,2)))/mean(out(in1,7).*zoneNum(in1,1)+out(in1,8).*zoneNum(in1,2))-1)*100)/(version+1);
WageChShort=(WageChShort*version+(mean(outnext(in,2)./out(in,2))-1)*100)/(version+1);
WageChLong=(WageChLong*version+(mean(out(in2,2))/mean(out(in1,2))-1)*100)/(version+1);
FracConstructChShort=(FracConstructChShort*version+(mean(((outnext(in,37)+outnext(in,38))./outnext(in,12))./((out(in,37)+out(in,38))./out(in,12)))-1)*100)/(version+1);
FracConstructBefore=(FracConstructBefore*version+mean((out(in,37)+out(in,38))./out(in,12))*100)/(version+1);
FracConstructAfter=(FracConstructAfter*version+mean((outnext(in,37)+outnext(in,38))./outnext(in,12))*100)/(version+1);
HoursWorkedChange=(HoursWorkedChange*version+(mean(outnext(in,12)./out(in,12))-1)*100)/(version+1);
EarningsChange=(EarningsChange*version+(mean((outnext(in,12).*outnext(in,2))./(out(in,12).*out(in,2)))-1)*100)/(version+1);
%Welfare
WelIndCh=-1+(WelfIndAlt./WelfInd).^exp0;
nanmean(sum(WelIndCh<0 & AgeInd<6 & repmat(in,1,500) & RenterInd==2,2)./sum(AgeInd<6 & repmat(in,1,500) & RenterInd==2,2))
nanmean(sum(WelIndCh<0 & AgeInd>15 & repmat(in,1,500) & RenterInd==2,2)./sum(AgeInd>15 & repmat(in,1,500) & RenterInd==2,2))
Age2OwnHurt=(Age2OwnHurt*version+nanmean(sum(WelIndCh<0 & AgeInd==2 & repmat(in,1,500) & RenterInd==2,2)./sum(AgeInd==2 & repmat(in,1,500) & RenterInd==2,2)))/(version+1);
Age14OwnHurt=(Age14OwnHurt*version+nanmean(sum(WelIndCh<0 & AgeInd==14 & repmat(in,1,500) & RenterInd==2,2)./sum(AgeInd==14 & repmat(in,1,500) & RenterInd==2,2)))/(version+1);
AvgBenefitInd=WelIndCh >0 & repmat(in1,1,500);
AvgBenefit=sum(AvgBenefitInd,'all')/500/sum(in1);
AvgOwnBenefitInd=WelIndCh >0 & RenterInd==2 & repmat(in1,1,500);
AvgOwnBenefit=nanmean(sum(AvgOwnBenefitInd,2)./sum(RenterInd==2 & repmat(in1,1,500),2));
AvgRentBenefitInd=WelIndCh>0 & RenterInd==1 & repmat(in1,1,500);
AvgRentBenefit=nanmean(sum(AvgRentBenefitInd,2)./sum(RenterInd==1 & repmat(in1,1,500),2));

% mean(AvgIncome1next(in)./AvgIncome1(in))-1
% mean(AvgIncome2next(in)./AvgIncome2(in))-1

OwnerHC=sum((RenterInd==2)./sum((RenterInd==2),2).*HCind,2);
OwnerOC=sum((RenterInd==2)./sum((RenterInd==2),2).*Cind,2);
OwnerHCChange=(mean(OwnerHC(in2))/mean(OwnerHC(in1))-1)*100;
OwnerOCChange=(mean(OwnerOC(in2))/mean(OwnerOC(in1))-1)*100;

wt=(RenterInd==2)./sum((RenterInd==2),2);
%x(8)=mean(ownnext(in)-own(in))*100;
% latex(x1,'%.2f');
%latex(vpa(sym(x1),4))
in1=out(:,1)==1 & [1:T]'>100;
in2=out(:,1)==2 & [1:T]'>100;

x2=(x2*version+(mean([out(in2,[2 3 4 10 11]) outnext(in2,7)-(1-deprH(1))*out(in2,7) outnext(in2,8)-(1-deprH(1))*out(in2,8) out(in2,10)./out(in2,3) out(in2,11)./out(in2,4) out(in2,7).*out(in2,10)./AvgIncome1(in2) out(in2,8).*out(in2,11)./AvgIncome2(in2) out(in2,7).*out(in2,3)./AvgIncome1(in2) out(in2,8).*out(in2,4)./AvgIncome2(in2) own(in2) ZoneOneFrac(in2)])./...
mean([out(in1,[2 3 4 10 11]) outnext(in1,7)-(1-deprH(1))*out(in1,7) outnext(in1,8)-(1-deprH(1))*out(in1,8) out(in1,10)./out(in1,3) out(in1,11)./out(in1,4) out(in1,7).*out(in1,10)./AvgIncome1(in1) out(in1,8).*out(in1,11)./AvgIncome2(in1) out(in1,7).*out(in1,3)./AvgIncome1(in1) out(in1,8).*out(in1,4)./AvgIncome2(in1) own(in1) ZoneOneFrac(in1)])-1)*100)/(version+1);

%latex(vpa(sym(x2),4))
%long_run=strjoin(arrayfun(@(x) num2str(x),x2,'UniformOutput',false),' & ');
%x(8)=1+mean(own(in2))-mean(own(in1));
% latex(100*(x-1),'%.2f');
%price/income and rent/income
%clear z; for t=1:T; in=AgeInd(t,:)<12; z(t,:)=[mean(WageInd(t,in)) mean(Cind(t,:)) mean(HresInd(t,:).*RentInd(t,:))]; end;
z=(out(:,12)/2000).*out(:,2)/(sum(sum(AgeInd<12))/sum(sum(AgeInd>0)));
znext=[z(2:end,:); z(end,:)];
py=4*mean(out(:,7)*2)*out(:,10)./z(:,1); ry=mean(out(:,7)*2)*out(:,3)./z(:,1);
pynext=[py(2:end); py(end)]; rynext=[ry(2:end); ry(end)];

%% 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%% frisch elasticity and housing supply elasticity %%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%frisch elasticity from agg:
fR=(1-alphaH+alphaH*(alphaH/((1-alphaH)*mean(out(:,3))))^(ElastCH/(1-ElastCH)))^(1/ElastCH);
n=mean(HoursInd(AgeInd<12));
c=mean(Cind(AgeInd<12));
h=mean(HresInd(AgeInd<12));
if abs(ElastCN)>.001 
 u=((fR^ElastCN)*(1-alphaN)*(c^ElastCN)+alphaN*(1-n)^ElastCN)^(1/ElastCN);
else
 u=((fR*c)^(1-alphaN))*((1-n)^alphaN);
end
L_agg=((1-n)/n)*(1-ElastCN-(fR^ElastCN)*(1-alphaN)*(1-gamma0-ElastCN)*((c/u)^ElastCN))/(gamma0*(1-ElastCN));
%frisch elasticity from ind
n=HoursInd;
c=Cind;
h=HresInd;
if abs(ElastCN)>.001
 u=((fR^ElastCN)*(1-alphaN)*(c.^ElastCN)+alphaN*(1-n).^ElastCN).^(1/ElastCN);
else
 u=((fR*c).^(1-alphaN)).*((1-n).^alphaN);
end
L=((1-n)./n).*(1-ElastCN-(fR^ElastCN)*(1-alphaN)*(1-gamma0-ElastCN)*((c./u).^ElastCN))/(gamma0*(1-ElastCN));
L=L(AgeInd<12 & n>0);
if version==0
    Lm=mean(L);
    L25=prctile(L,25);
    L75=prctile(L,75);
else
    Lm=(Lm*version+mean(L))/(version+1);
    L25=(L25*version+prctile(L,25))/(version+1);
    L75=(L75*version+prctile(L,75))/(version+1);
end
% %housing supply
% h0=mean(H1+H2)/mean(H1bar+H2bar);
% h1=mean(H1)/mean(H1bar);
% h2=mean(H2)/mean(H2bar);
% if version==0
%     HSE=RTSH0loc2/(1-RTSH0loc2+h0/(1-h0)+RTSH0loc2*0.25);
%     HSEone=RTSH0loc2/(1-RTSH0loc2+h1/(1-h1)+RTSH0loc2*0.25);
%     HSEtwo=RTSH0loc2/(1-RTSH0loc2+h2/(1-h2)+RTSH0loc2*0.25);
%     HbaroneDist=(mean(H1bar)-mean(H1))/mean(H1bar);
%     HbartwoDist=(mean(H2bar)-mean(H2))/mean(H2bar);
% else
%     HSE=(HSE*version+RTSH0loc2/(1-RTSH0loc2+h0/(1-h0)+RTSH0loc2*0.25))/(version+1);
%     HSEone=(HSEone*version+RTSH0loc2/(1-RTSH0loc2+h1/(1-h1)+RTSH0loc2*0.25))/(version+1);
%     HSEtwo=(HSEtwo*version+RTSH0loc2/(1-RTSH0loc2+h2/(1-h2)+RTSH0loc2*0.25))/(version+1);
%     HbaroneDist=(HbaroneDist*version+(mean(H1bar)-mean(H1))/mean(H1bar))/(version+1);
%     HbartwoDist=(HbartwoDist*version+(mean(H2bar)-mean(H2))/mean(H2bar))/(version+1);
% end
end

%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%% Create Handles in Latex%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

if mode==1
    if model==1
        % Table 1 Parameters
        fID = fopen('../Figures/Parameters.tex','w');
        % Panel A
        fprintf(fID,'\\newcommand{\\IncStates}{%4.3f %4.3f %4.3f}\n',IncStates(1:3))  ; 
        fprintf(fID,'\\newcommand{\\psiz}{%4.3f %4.3f %4.3f}\n',SSIdist(1:3))  ; 
        fprintf(fID,'\\newcommand{\\taxss}{%4.2f}\n',taxss)  ; 
        % Panel B
        fprintf(fID,'\\newcommand{\\PbetaL}{%4.3f}\n',BetaRel(1)*beta)  ; 
        fprintf(fID,'\\newcommand{\\PbetaH}{%4.3f}\n',BetaRel(2)*beta)  ;
        fprintf(fID,'\\newcommand{\\Pgamma}{%4.2f}\n',gamma0)  ; 
        fprintf(fID,'\\newcommand{\\alphaC}{%4.2f}\n',alphaC)  ; 
        fprintf(fID,'\\newcommand{\\alphaH}{%4.2f}\n',alphaH)  ; 
        fprintf(fID,'\\newcommand{\\alphaN}{%4.2f}\n',alphaN)  ; 
        fprintf(fID,'\\newcommand{\\ElastCN}{%4.2f}\n',ElastCN)  ; 
        fprintf(fID,'\\newcommand{\\ElastCH}{%4.2f}\n',ElastCH)  ; 
        fprintf(fID,'\\newcommand{\\HoursMinbyHours}{%4.2f}\n',HoursMin)  ;
        fprintf(fID,'\\newcommand{\\Ptheta}{%4.2f}\n',Theta)  ;        
        % Panel C
        fprintf(fID,'\\newcommand{\\PQ}{%4.3f}\n',PriceBond)  ; 
        fprintf(fID,'\\newcommand{\\Pkappa}{%4.2f}\n',thetaRes)  ; % thetaRes=thetaInv
        fprintf(fID,'\\newcommand{\\thetaRes}{%4.2f}\n',thetaRes)  ; 
        fprintf(fID,'\\newcommand{\\thetaInv}{%4.2f}\n',thetaInv)  ; 
        fprintf(fID,'\\newcommand{\\tauP}{%4.2f}\n', taxprop(1,1)*100)  ; 
        fprintf(fID,'\\newcommand{\\deprH}{%4.4f}\n',deprH(1))  ; 
        fprintf(fID,'\\newcommand{\\HresMinbyHresRatio}{%4.2f}\n',HresMinbyHres)  ; 
        % Panel D
        fprintf(fID,'\\newcommand{\\RTSC}{%4.2f}\n',RTSC)  ; 
        % fprintf(fID,'\\newcommand{\\RTSH0loc1}{%4.2f}\n',RTSH0loc1)  ; 
        % fprintf(fID,'\\newcommand{\\RTSH0loc2}{%4.2f}\n',RTSH0loc2)  ; 
        fprintf(fID,'\\newcommand{\\HBARone}{%4.2f}\n',HBARloc1(1))  ; 
        fprintf(fID,'\\newcommand{\\HBARtwo}{%4.2f}\n',HBARloc2(1))  ;
        fprintf(fID,'\\newcommand{\\PphiT}{%4.3f}\n',CommCost)  ; 
        fprintf(fID,'\\newcommand{\\PphiF}{%4.3f}\n',CommCostFinbyInc)  ;    
        fprintf(fID,'\\newcommand{\\OOTElas}{%4.3f}\n',HFgrid1(2,1))  ; 
        fprintf(fID,'\\newcommand{\\OOTLevel}{%4.3f %4.3f}\n',[HFgrid0(2,1); HFgrid0(2,2)])  ; 
        fprintf(fID,'\\newcommand{\\Ppi}{%4.2f}\n', TrHFProb)  ;
        fprintf(fID,'\\newcommand{\\PchiAll}{%4.2f}\n',Z1shiftAll)  ; 
        fprintf(fID,'\\newcommand{\\PchiW}{%4.2f}\n',Z1shiftSize(1))  ; 
        fprintf(fID,'\\newcommand{\\PchiR}{%4.2f}\n',Z1shiftSize(2))  ; 
        fprintf(fID,'\\newcommand{\\Pchibar}{%4.2f}\n',Z1shiftCut(1))  ; 
        
        % Calibration Section
        % Demographics
        fprintf(fID,'\\newcommand{\\fracRet}{%4.1f}\n',fracRet*100)  ;     
        
        % Labor Income
        fprintf(fID,'\\newcommand{\\HoursMinBind}{%4.2f}\n',HoursMinBind*100)  ;
        fprintf(fID,'\\newcommand{\\taxssper}{%4.0f}\n',taxss*100)  ; 
        fprintf(fID,'\\newcommand{\\Ppsizone}{%4.2f}\n',SSIdist(1))  ;
        fprintf(fID,'\\newcommand{\\Ppsiztwo}{%4.2f}\n',SSIdist(2))  ;
        fprintf(fID,'\\newcommand{\\Ppsizthree}{%4.2f}\n',SSIdist(3))  ;
        fprintf(fID,'\\newcommand{\\RetInc}{%s}\n',addComma(round(RetInc)))  ;
        fprintf(fID,'\\newcommand{\\RetIncbyLabInc}{%4.2f}\n',RetIncbyLabInc*100)  ;
        
        % Preferences
        fprintf(fID,'\\newcommand{\\AvgHours}{%4.1f}\n',AvgHours*100)  ;
        fprintf(fID,'\\newcommand{\\HousTotConsratio}{%4.1f}\n',HousTotConsratio*100)  ;
        fprintf(fID,'\\newcommand{\\FrischEMacro}{%4.2f}\n',L_agg)  ;
        fprintf(fID,'\\newcommand{\\FrischEMicro}{%4.2f}\n',Lm)  ;
        
        fprintf(fID,'\\newcommand{\\PbetaLy}{%4.3f}\n',PbetaLy)  ; 
        fprintf(fID,'\\newcommand{\\PbetaHy}{%4.3f}\n',PbetaHy)  ; 
        fprintf(fID,'\\newcommand{\\Pbeta}{%4.2f}\n',0.75*BetaRel(1)*beta + 0.25*BetaRel(2)*beta)  ; 
        fprintf(fID,'\\newcommand{\\NWbyInc}{%4.2f}\n',NWbyInc)  ; 
        fprintf(fID,'\\newcommand{\\GiniNW}{%4.2f}\n',GiniNW)  ;   
        
        fprintf(fID,'\\newcommand{\\Probbequest}{%4.1f}\n',Probbequest*100)  ;
        fprintf(fID,'\\newcommand{\\fracbeqann}{%4.1f}\n',fracbeqann*100)  ;
        
        fprintf(fID,'\\newcommand{\\PchiAllchiR}{%4.2f}\n',Z1shiftAll*Z1shiftSize(2))  ; 
        fprintf(fID,'\\newcommand{\\fracRetRel}{%4.2f}\n',fracRetRel)  ; 
        fprintf(fID,'\\newcommand{\\IncRel}{%4.2f}\n',IncRel)  ; 
        fprintf(fID,'\\newcommand{\\MedMktRentbySqftRel}{%4.2f}\n',MedMktRentbySqftRel)  ; 
        fprintf(fID,'\\newcommand{\\HORel}{%4.2f}\n',HORel)  ; 
        fprintf(fID,'\\newcommand{\\cbarFrac}{%4.1f}\n',cbarFrac*100)  ;     
        
        % Production and Housing
        fprintf(fID,'\\newcommand{\\HSE}{%4.2f}\n',HSE)  ; 
        fprintf(fID,'\\newcommand{\\HSEone}{%4.2f}\n',HSEone)  ; 
        fprintf(fID,'\\newcommand{\\HSEtwo}{%4.2f}\n',HSEtwo)  ;     
        fprintf(fID,'\\newcommand{\\HoverHbar}{%4.2f}\n',h0)  ;
        fprintf(fID,'\\newcommand{\\HbaroneDist}{%4.1f}\n',HbaroneDist*100)  ; 
        fprintf(fID,'\\newcommand{\\HbartwoDist}{%4.1f}\n',HbartwoDist*100)  ;
        
        fprintf(fID,'\\newcommand{\\tauPy}{%4.2f}\n', taxprop(1,1)*100/4)  ; 
        fprintf(fID,'\\newcommand{\\ImInt}{%4.2f}\n',((1/PriceBond)^(1/4)-1)*100)  ;       
        fprintf(fID,'\\newcommand{\\MedMktPHbyMedMktRent}{%4.2f}\n',MedMktPHbyMedMktRent);
        fprintf(fID,'\\newcommand{\\HresMin}{%s}\n',addComma(round(HresMin)))  ; 
        fprintf(fID,'\\newcommand{\\HresMinbyHres}{%4.1f}\n',HresMinbyHres*100)  ; 
        
        % Commuting Costs
        fprintf(fID,'\\newcommand{\\CommCost}{%4.1f}\n',CommCost*100)  ; 
        fprintf(fID,'\\newcommand{\\CommCostFinDollar}{%s}\n',addComma(round(CommCostFinDollar)))  ; 
        fprintf(fID,'\\newcommand{\\CommCostFinbyInc}{%4.1f}\n',CommCostFinbyInc*100)  ; 
       
        % Baeline Model Results
        % Earnings, Wealth, and Home Ownership
        fprintf(fID,'\\newcommand{\\AvgOwnRate}{%4.1f}\n',OwnRate)  ;
        fprintf(fID,'\\newcommand{\\AvgOwnRateA}{%4.1f}\n',OwnRateAfter)  ;
        fprintf(fID,'\\newcommand{\\AvgOwnRateB}{%4.1f}\n',OwnRateBefore)  ;
        fprintf(fID,'\\newcommand{\\GiniInc}{%4.2f}\n',GiniInc)  ;

%         % Short-run Resposne
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'RoneP}','{%4.1f}\n']),x1(2))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'RtwoP}','{%4.1f}\n']),x1(3))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PoneP}','{%4.1f}\n']),x1(4))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PtwoP}','{%4.1f}\n']),x1(5))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVoneP}','{%4.1f}\n']),x1(6))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVtwoP}','{%4.1f}\n']),x1(7))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PoneByRoneP}','{%4.1f}\n']),x1(8))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PtwoByRtwoP}','{%4.1f}\n']),x1(9))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPoneByYP}','{%4.1f}\n']),x1(10))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPtwoByYP}','{%4.1f}\n']),x1(11))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRoneByYP}','{%4.1f}\n']),x1(12))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRtwoByYP}','{%4.1f}\n']),x1(13))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'OwnP}','{%4.1f}\n']),x1(14))  ;
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'ZoneOneFracP}','{%4.1f}\n']),x1(15))  ;     
         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelP}','{%4.2f}\n']),abs(x1(16)))  ;     
         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelRP}','{%4.2f}\n']),abs(x1(17)))  ;     
         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelOP}','{%4.2f}\n']),abs(x1(18)))  ;     
%         
%         % Long-run Resposne
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRoneP}','{%4.1f}\n']),x2(2))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRtwoP}','{%4.1f}\n']),x2(3))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPoneP}','{%4.1f}\n']),x2(4))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwoP}','{%4.1f}\n']),x2(5))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVoneP}','{%4.1f}\n']),x2(6))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVtwoP}','{%4.1f}\n']),x2(7))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPoneByRoneP}','{%4.1f}\n']),x2(8))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwoByRtwoP}','{%4.1f}\n']),x2(9))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPoneByYP}','{%4.1f}\n']),x2(10))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPtwoByYP}','{%4.1f}\n']),x2(11))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRoneByYP}','{%4.1f}\n']),x2(12))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRtwoByYP}','{%4.1f}\n']),x2(13))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSOwnP}','{%4.1f}\n']),x2(14))  ;     
%         fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSZoneOneFracP}','{%4.1f}\n']),x2(15))  ;     
        
        %Welfare
        fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AgeTwoOwnHurt}','{%4.2f}\n']),Age2OwnHurt*100)  ;     
        fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AgeForteenOwnHurt}','{%4.2f}\n']),Age14OwnHurt*100)  ;     
        fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AvgBenefit}','{%4.0f}\n']),AvgBenefit*100)  ;     
        fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AvgOwnBenefit}','{%4.0f}\n']),AvgOwnBenefit*100)  ;     
        fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AvgRentBenefit}','{%4.0f}\n']),AvgRentBenefit*100)  ;     

        fprintf(fID,'\\newcommand{\\TaxbyInc}{%4.1f}\n',TaxbyInc*100)  ; 

        fprintf(fID,'\\newcommand{\\ZOneHIncrease}{%4.1f}\n',Z1HIncrease*100)  ;
%         fprintf(fID,'\\newcommand{\\PYZOneA}{%4.2f}\n',PYZ1A)  ;
%         fprintf(fID,'\\newcommand{\\PYZOne}{%4.2f}\n',PYZ1)  ;
%         fprintf(fID,'\\newcommand{\\PYZTwoA}{%4.2f}\n',PYZ2A)  ;
%         fprintf(fID,'\\newcommand{\\PYZTwo}{%4.2f}\n',PYZ2)  ;
        %Statistics in Section 5
        
        fprintf(fID,'\\newcommand{\\NWMidChZoneOne}{%4.1f}\n',abs(NWindMid1Ch1))  ;
        fprintf(fID,'\\newcommand{\\WageMidChZoneOne}{%4.1f}\n',abs(WageIndMid1Ch1))  ;
        fprintf(fID,'\\newcommand{\\OwnLocalChangeZoneOne}{%4.1f}\n',abs(OwnLocalChangeZ1))  ;
        fprintf(fID,'\\newcommand{\\OwnLocalChangeZoneTwo}{%4.1f}\n',abs(OwnLocalChangeZ2))  ;
        fprintf(fID,'\\newcommand{\\SizeChShort}{%4.1f}\n',SizeChShort)  ;
        fprintf(fID,'\\newcommand{\\SizeChLong}{%4.1f}\n',SizeChLong)  ;
        fprintf(fID,'\\newcommand{\\WageChShort}{%4.1f}\n',WageChShort)  ;
        fprintf(fID,'\\newcommand{\\WageChLong}{%4.1f}\n',WageChLong)  ;
        fprintf(fID,'\\newcommand{\\FracConstructChShort}{%4.1f}\n',FracConstructChShort)  ;
        fprintf(fID,'\\newcommand{\\FracConstructBefore}{%4.1f}\n',FracConstructBefore)  ;
        fprintf(fID,'\\newcommand{\\FracConstructAfter}{%4.1f}\n',FracConstructAfter)  ;
        fprintf(fID,'\\newcommand{\\HoursWorkedChange}{%4.1f}\n',abs(HoursWorkedChange))  ;
        fprintf(fID,'\\newcommand{\\EarningsChange}{%4.1f}\n',abs(EarningsChange))  ;        
        fprintf(fID,'\\newcommand{\\OwnerHCChange}{%4.1f}\n',OwnerHCChange)  ;        
        fprintf(fID,'\\newcommand{\\OwnerOCChange}{%4.1f}\n',OwnerOCChange)  ;        
      
        %Housing
%         fprintf(fID,'\\newcommand{\\OwnRate}{%4.2f}\n',OwnRate*100); 
%         fprintf(fID,'\\newcommand{\\OwnRatePrior}{%4.2f}\n',OwnRatePrior*100); 
        % fprintf(fID,'\\newcommand{\\chi0}{%4.2f}\n',chi0)  ; 

        % fprintf(fID,'\\newcommand{\\TrProbDZ11p}{%4.2f}\n',TrProbDZ11)  ; 
        % fprintf(fID,'\\newcommand{\\TrProbDZ22p}{%4.2f}\n',TrProbDZ22)  ; 
        % fprintf(fID,'\\newcommand{\\TrProbDZ33p}{%4.2f}\n',TrProbDZ33)  ; 
        % fprintf(fID,'\\newcommand{\\TrProbDZ44p}{%4.2f}\n',TrProbDZ44)  ;
        % beta
       fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AgeFourtyWelR}','{%4.2f}\n']),abs(y1(5,2)))  ;     
       fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AgeSeventyFiveWelR}','{%4.2f}\n']),abs(y1(14,2)))  ;     
       fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AgeFourtyWelO}','{%4.2f}\n']),abs(y1(5,3)))  ;     
       fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'AgeNinetyFiveWelO}','{%4.2f}\n']),abs(y1(19,3)))  ;     

        % Commuting cost

        % fprintf(fID,'\\newcommand{\\deprINV0}{%4.2f}\n',deprINV0)  ; 
        %Results
        %fprintf(fID,'\\newcommand{\\short_run}{%s}\n', short_run)  ; 
        %fprintf(fID,'\\newcommand{\\long_run}{%s}\n', long_run)  ; 
        fclose(fID);
    end
    
    %Table 2
     fID = fopen(join(['../Figures/Table2',num2str(model_space(model)),'.tex']),'w');
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'W}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(1))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Rone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(2))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Rtwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(3))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Pone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(4))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Ptwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(5))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(6))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVtwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(7))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PoneByRone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(8))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PtwoByRtwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(9))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPoneByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(10))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPtwoByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(11))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRoneByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(12))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRtwoByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(13))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Own}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(14))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'ZoneOneFrac}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(15))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Wel}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(16))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelR}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(17))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelO}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(18))  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'W}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(1)),x1(1)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Rone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(2)),x1(2)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Rtwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(3)),x1(3)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Pone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(4)),x1(4)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Ptwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(5)),x1(5)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Pluxury}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(6)),x1(6)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(7)),x1(7)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVtwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(8)),x1(8)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVluxury}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(9)),x1(9)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PoneByRone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(10)),x1(10)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PtwoByRtwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(11)),x1(11)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPoneByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(12)),x1(12)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPtwoByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(13)),x1(13)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRoneByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(14)),x1(14)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRtwoByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(15)),x1(15)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Own}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(16)),x1(16)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'ZoneOneFrac}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(17)),x1(17)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'ZoneTwoFrac}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(18)),x1(18)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'ZoneLuxuryFrac}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(19)),x1(19)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Wel}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(20)),x1(20)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelR}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(21)),x1(21)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelO}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(22)),x1(22)])  ;   

%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSW}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(1))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(2))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRtwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(3))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(4))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(5))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(6))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVtwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(7))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPoneByRone}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(8))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwoByRtwo}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(9))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPoneByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(10))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPtwoByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(11))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRoneByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(12))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRtwoByY}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(13))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSOwn}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(14))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSZoneOneFrac}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x2(15))  ;   
%     

%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSW}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(1)),x2(1)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(2)),x2(2)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRtwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(3)),x2(3)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(4)),x2(4)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(5)),x2(5)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(6)),x2(6)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVtwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(7)),x2(7)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPoneByRone}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(8)),x2(8)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwoByRtwo}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(9)),x2(9)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPoneByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(10)),x2(10)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPtwoByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(11)),x2(11)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRoneByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(12)),x2(12)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRtwoByY}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(13)),x2(13)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSOwn}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(14)),x2(14)])  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSZoneOneFrac}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x2(15)),x2(15)])  ;   
% 

   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'W}','{%4.3f}\n']),x1(1))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Rone}','{%4.3f}\n']),x1(2))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Rtwo}','{%4.3f}\n']),x1(3))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Pone}','{%4.3f}\n']),x1(4))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Ptwo}','{%4.3f}\n']),x1(5))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVone}','{%4.3f}\n']),x1(6))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'INVtwo}','{%4.3f}\n']),x1(7))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PoneByRone}','{%4.3f}\n']),x1(8))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'PtwoByRtwo}','{%4.3f}\n']),x1(9))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPoneByY}','{%4.3f}\n']),x1(10))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HPtwoByY}','{%4.3f}\n']),x1(11))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRoneByY}','{%4.3f}\n']),x1(12))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'HRtwoByY}','{%4.3f}\n']),x1(13))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Own}','{%4.3f}\n']),x1(14))  ;
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'ZoneOneFrac}','{%4.3f}\n']),x1(15))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'Wel}','{%4.3f}\n']),x1(16))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelR}','{%4.3f}\n']),x1(17))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'WelO}','{%4.3f}\n']),x1(18))  ;     
% 
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSW}','{%4.3f}\n']),x2(1))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRone}','{%4.3f}\n']),x2(2))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSRtwo}','{%4.3f}\n']),x2(3))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPone}','{%4.3f}\n']),x2(4))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwo}','{%4.3f}\n']),x2(5))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVone}','{%4.3f}\n']),x2(6))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSINVtwo}','{%4.3f}\n']),x2(7))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPoneByRone}','{%4.3f}\n']),x2(8))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSPtwoByRtwo}','{%4.3f}\n']),x2(9))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPoneByY}','{%4.3f}\n']),x2(10))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHPtwoByY}','{%4.3f}\n']),x2(11))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRoneByY}','{%4.3f}\n']),x2(12))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSHRtwoByY}','{%4.3f}\n']),x2(13))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSOwn}','{%4.3f}\n']),x2(14))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(model_space(model)),'SSZoneOneFrac}','{%4.3f}\n']),x2(15))  ;     
%     
    fclose(fID);
    
elseif mode==2
    fID = fopen('../Figures/Table3.tex','a+');
%     fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'Wel}','{%4.3f}\n']),x1(16))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelR}','{%4.3f}\n']),x1(17))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelO}','{%4.3f}\n']),x1(18))  ;     
%     fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'Welfare}','{%4.3f}\n']),Welfare)  ; 
%     fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'Wel}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(16))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelR}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(17))  ;   
%     fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelO}[1]{\\num[round-mode=places,round-precision=#1]','{%4.4f}}\n']),x1(18))  ;   

    fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'Wel}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(16)),x1(16)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelR}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(17)),x1(17)])  ;   
    fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelO}[2]{\\ifnum #2=1 \\num[round-mode=places,round-precision=#1]{%4.4f} \\else \\num[round-mode=places,round-precision=#1]','{%4.4f}\\fi}\n']),[abs(x1(18)),x1(18)])  ;   
    fclose(fID);
%     fID = fopen('..\Figures\Table3.tex','r');
%     Text = textscan(fID, '%s', 'Delimiter', '\n');  
%     result = Text{1};
%     a = regexp(result,'dsadsadasdasdas')
%     fclose(fID);
% tline = fgetl(fID);
% lineCounter = 1;
% while ischar(tline)
%     disp(tline)
%     if strcmp(tline, 'FxTB')
%         break;
%     end
%     % Read next line
%     tline = fgetl(fid);
%     lineCounter = lineCounter + 1;
% end
% fclose(fid);
else
    write=1;
    if write==0
        fID = fopen('../Fortran Output/Table4/table4.txt','a+');
        fprintf(fID,join([num2str(model_space(model)),'-tax_neutral_rate-','{%4.5f}\n']),tax_neutral)  ;     
        fclose(fID);
    else
        fID = fopen('../Figures/Table4.tex','a+');
        fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'Wel}','{%4.3f}\n']),x1(16))  ;     
        fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelR}','{%4.3f}\n']),x1(17))  ;     
        fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'WelO}','{%4.3f}\n']),x1(18))  ;     
        fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'Welfare}','{%4.3f}\n']),Welfare)  ;
        fprintf(fID,join(['\\newcommand{\\',num2str(latex_macro_name(model)),'Tax}','{%4.2f}\n','\%']),tax_neutral*100)  ;     
        fclose(fID);
    end
end 
end
%                             H1        H2       n1        n2
%rhoh=0.5, H1bar=10, H2bar=10:   98.0392   98.0392  250.0000  250.0000
%rhoh=0.5, H1bar=5,  H2bar=15:   94.9903   99.8938  243.7500  256.2500 --> z1 changed to 25% of space but still has 48.75% of population and housing
%rhoh=1.0, H1bar=10, H2bar=10:   39.6825   39.6825  250.0000  250.0000
%rhoh=1.0, H1bar=5,  H2bar=15:   19.8413   59.5238  125.0000  375.0000 --> z1 changed to 25% of space and now has 25% of population and housing