!2016/03/01
!-This code gets same results as analytic solution for Renters (iRenter=1)
!-This code gets same results as analytic Renter's solution for owners (iRenter=2) when return on housing is equal to the risk free rate
!-When rent is relatively high, renters choose cheaper location. When minimum rent (across both locations) is relatively high: renters consume more, work less, and choose smaller houses
!-When price is relatively high, owners choose cheaper location. When the minimum price (across both locations) is relatively high: owners choose less residential and investment property
!-(done) Add depreciation to PRgrid, calculation of NWnext, and optimal residential choice
!-(done) Check that renter's solution is identical to analytic solution when no constraints and no risk
!-(done) Check that owner's solution is identical to renter's solution and owner is indifferent about
! real estate share in portfolio when no constraints, no risk, and no owner/renter depreciation differneces
!-(done) Check that policy functions make sense for different prices
!-Code up to this point is saved as ModelOfCityOld20160307.f
!2016/03/08
!-(done) Add age dependent labor income profile (AgeProd), social security tax (tax), pension (Pension), retirement (if iAge<=iRet then: Hours=0, LaborIncome=Pension, not dividing NWnext by DZgrid)
!-(done) Check that this code is identical to ModelOfCityOld20160307.f if nRet=0, AgeProd=1, tax=0, Pension=0, and Hours>0 constraint is absent
!2016/03/09
!-(done) N>0, budget constraint, and downpayment constraint. Put in if statements consistent w/ lagrange multipliers binding
! -(done) Renter: If Hnext<0 then Hnext=0. If Bnext<0, then set U=minval.
! -(done) Onwer: If Hnext<0 then Hnext=0. If ColConstr violated, then set Hres=Hres0; if Hres0<0, then set U=minval. Here Hres0 is the value that makes the collateral constraint bind
!-(done) Add code to write policy and value functions: pol01.txt,pol02.txt ...
!-(done) Make policy include the optimal Cchoice and Hchoice conditional on any combination of (iRenter,iLOC), not just for the best combination
!-(done) getpolicy is built. for every choice of (iRenter,iLOC) it computes interpolated ValFun, C, Hinv and then chooses the best (iRenter,iLOC)
!-(done) Checked that when N>0, budget constraint, downpayment constraint are all commented out, then solution is identical to analytic
!-(done) Checked that (if redefine PR1grid and PR2grid to be prices rather than price/rent ratios) agent chooses to rent when rent is relatively low and to own when price is relatively low; agent chooses the cheaper location; agent chooses more housing consumption when rent and/or price are low; more housing investment when price is low.
!2016/03/24
!-(done) DP: added an extra calculation of Util inside if statement where Hres is changed (when collateral constraint binds)
!-(done) Began building Simulate. It can now call getpolicy for some initital inputs.
!-(done) Checked that:
!        a) Higher wage leads to higher hours and consumption
!        b) Higher price and rent in zone 1 shifts housing to zone 2 (and vice versa)
!        c) Higher price/rent (for a given rent) shifts housing towards renting and less investment; lower price/rent shifts housing towards owning and more investment
!        d) When rents are same in both zones but price in zone 1 is higher, all owners shift to zone 2
!2016/03/27
! -(done) In definition of RP1grid, it was RP1grid(nRent1) instead of RP1grid(nRP1), now fixed
! -(done) In DP changed multH1=RPnextMult(iAgg,iHFnext) to H1nextMult(iAgg,iHFnext) and same for H2
! -(done) Changed all references to H1 and H2 to H1last and H2last in Simulate and GetPolicy (no changes made to DP)
! -(done) Changed notation so that H1grid and H2grid are the per capita average housing quantites so that H1=H1grid*nAgents
! -(done) In simulation added calculation of production side: HoursDemand,H1,H2 (and some intermediate quantities)
!2016/04/26
! -(done) Changed all labels from PR (price rent) to RP (risk premium)
! -(done) In DP created recursion to compute PH(iAgg)=Rent(iAgg)+E[PH(iAgg,iHFnext)]/(rf+RP(iAgg)). This computes PH1grid(iAgg,1) and PH2grid(iAgg,1) (and writes them to text). Also computes PH1nextGrid(iAgg,iHFnext), PH2nextGrid(iAgg,iHFnext).
!   -(done) Test that the prices computed make sense (should be equal to Rent/(RF-1) when no risk premium and smaller when risk premium
!   -(done) Test that policy and value functions are consistent w/ previous code
! -(done) In DP, changed some of the if statements for when something is out of bounds - this ensures that agents w/ very small wealth and utility aren't buying investment property
! -(done) Checked that when RP=0, agent is indifferent b/w renting, owning w/ Hinv=0, or owning w/ Hinv>0 (as long as the down payment constraints aren't violated)
! -(done) In DP, force Hchoice=0 when RP=0. Later need to check that this is optimal (if housing is a good enough hedge, there may be demand for investment property at zero or even negative risk premiums). Can check this by expeding RPgrid to have negative values
! -(done) In Simulate read PH1grid and use them to compute prices from Rent and RP
! -(done) Add market clearing inside Simulate (no need for separate function)
!   -Market clearing process seems to work well when restricted to one zone only (ie H2last=0 and RTSH0loc2=0). Prices converge and all markets clear
!   -Market clearing also seems to work well when allowing for both zones. Prices converge. Labor market clears. The housing and rental market don't quite clear. Housing supply converges but housing demand hops around the supply - this happens because agents are indifferent so a small change in prices causes them to jump from one zone to another. Similarly, in the rental market supply and demand hop around what i think are the equilibrium values - again hopping around happens due to indifference
!2016/04/27
! -(done) Added periods, indexed by t. Added Xlast and/or Xnext so that the period t+1 variable is computed at the end of period t
! -(done) Improved how RP is updated
! -(done) Added tiebreaker to improve market clearing
! -(done) Fixed several mistakes involving nRet when selecting who is working/retiring and computing PensionTax in Simulate
! -(done) In Simulate, Pension=PensionTax/NumRetired where PensionTax=tax*sum(LaborIncome). An alternative is compute PensionBelief from interpolating PensionGrid. It should be that Pension=PensionGrid once everything is converged
! -(done) In Simulate, H1 and H2 are defined as total (as opposed to per capita) housing. However, H1grid and H2grid are defined as per capita. Therefore, when sending H1last and H2last to interpAgg and getpolicy, need to send H1last/real(nAgent) and H2last/real(nAgent)
! -This version is ready to simulate. Seems that several problems while simulating:
!  -Age=15 agents have Bnext around 0.8. This was because NWgrid(7)=-0.00001 and NWgrid(8)=0.8 so they were getting very negative utility from being just below 0. Now fixed, but must have a gridpoint on NWgrid just above 0.
!  -Once simulation gets going, everyone is renting and no one is buying investment property despite high premium. Fixed. Needed to extend premium grid. Equilibrium premium is very high because, due to PIH, agents have near zero wealth. Buying a house requires very high leverage, thus even small shocks may violate borrowing constraint
!  -Once simulation gets going, NW becomes negative. I think this is due to interpolation issue: When Bnext=0 (last year of life), due to Hours>=0 constraint, Cons as a function of NW is convex, thus interpolation leads to too high consumption, which in turn leads to Bnext<0. How to fix? Maybe spline or finer NWgrid.
!2016/05/23:
! -(done) Add computation of derivatives of Policy w/ respect to NW for spline interpolation. Compute consumption policy using spline --> seems to work better
! -(done) Change tiebreaker to be multiplicative rather than additive - otherwise scale of value function affects necessary size of tiebreaker
! -(done) Added ValFunInd to the output of getpolicy
! -(done) Checked that if 1) Beliefs about future (Wage,Rent,RP) are constant, 2) Simulated quantities are identical to beliefs, 3) beta=PriceDebt then (consistent w/ Permanent Income Hypothesis) an agent starting w/ NW>0 slowly draws it down to zero by death, s.t. C and Hres are (approximately) constant
! -(done) Fixed problem in calculation of prices from risk premia. Depr was in the wrong place: multiplied Rent instead of E[PHnext]
! -(done) Changed initialization of RenterInd (was mistakenly initializing RenterIndLast)
! -(done) Changed market clearing process: 1) Added WageLast,Rent1last,etc so that to quit iteration once prices are not changing by much, 2) changed the speed at which updating happens
! -(done) Added foreign demand to market clearing process. This only affects owners in zone 1 because foreigners do not buy housing and do not rent out their housing.
! -(done) Added output and outputWelf, which are written to temp01.txt and temp02.txt
! -(done) Set theta=1 (was .8 before). Otherwise was making renting preferential to owning when should have been indifferent
! -(done) Changed Cchoice process when iCchoice<nCchoice0+1. Now have Cmin=0.001 and Cmax=1.05*(LaborIncome+max(.01,NW))+.05. Also added Cint
! -(done) Added if(Hres.lt.0.001) Hres=0.001 where collateral constraint is violated
! -(done) AgeProd(iAge) changed to AgeProd(nAge+1-iAge) in DP
! -(done) When computing labor supply (Hours), changed to Sum(HoursInd*AgeProd) from Sum(HoursInd)
! -(done) There were issues w/ nRet, this is now fixed. If Age>=nWork-nRet, ZindNext=Zind (both DP and Simulate)
! -(done) Added constants to production function for scaling reasons. Before had: Y(H,RTS)=H^RTS --> P*RTS*(H^(RTS-1))=Wage --> Hdem=(P*RTS/Wage)^(1/(1-RTS))
!         Changed to: Y(H,RTS)=(1/a)*N*(H/N)^RTS=(1/a)*(N^(1-RTS))*(H^RTS) -->  Wage=(N^(1-RTS))*(P*RTS/a)*(H^(RTS-1))=(P*RTS/a)*((H/N)^(RTS-1))
!         Hdem=N*(P*RTS/(a*Wage))^(1/(1-RTS)) --> Hdem is linear in N
!         Suppose Hsup(i)=1/Wage --> Hsup=N/Wage --> market clearing Wage is independent of N --> Wage=(P*RTS/a)^(1/RTS) --> Hdem=N*(P*RTS/a)^(-1/RTS) --> Y=N/(P*RTS) --> Y is linear in N
! -(done) Changed calibration: h=(1/Rent)*(aH/aC)*c --> avg housing expenditure roughly 40% of consumption basket --> h*Rent/c=aH/aC=2/3 --> aH=(2/3)*aC
!         n*Wage=c+Rent*h --> income=expenditure --> n*Wage=c+(aH/aC)*c=c*(aC+aH)/aC
!         n=1-(1/Wage)*(aN/aC)*c --> n=1-(1/Wage)*(aN/aC)*(aC/(aC+aH))*n*Wage=1-n*(aN/(aC+aH)) --> n=(aC+aH)/(aC+aH+aN)=1/3 --> avg hours worked 1/3 of all available
!         combine: aC+aH+aN=1 --> aC+aH=1/3 and aH=(2/3)*aC --> aC*5/3=1/3 --> aC=3/15, aH=2/15, aN=10/15
! -Build beliefs:
!  -(done) New subroutine Beliefs which computes regression coefficients
!    -Within this, belief about Pension is computed, unlike other beliefs (which are conditional on (iHF,iHFnext)), this belief is conditional on iHF only
!    -Need to check if pension belief working right
!  -(done) In DP use beliefs to update next period's values of state variables
!  -(done) Get rid of some of the references to PensionGrid because now using beliefs from linear function, however add write(PensionGrid) after it is computed in DP
!  -(done) Added CoefsMin and CoefsMax to restrict beliefs. However, can't use them because if WageNext(1) is unrestricted but WageNext(2) is restricted, then interpolated value will be different from the value implied by the regression.
!  -This needs testing
!2016/06/01
! -(done) Got rid of all references to deprINV1
! -(done) Added calculation of PHnextMin(iLOC)=minimum possible price next period
! -(done) Changed borrowing constraint to B(t+1)>-thetaRes*Hres*(1-deprH)-thetaInv*Hinv*(1-deprH-deprINV0). Note that this implies that NW>0 if theta<1. Thus changed grid to reflect this
! -(done) Changing the borrowing constraint also required changing the if statement that determines what to do when constraint violated
! -(done) To this if statement, added an extra piece of code, in case the recalculated Hres (when set to 0.01) still violated the constraint
! -(done) In simulate added code so that Zind=1 for newborns
! -(done) Add 1/zind to hoursind; zind to hours, pension, and laborincomeind calculations
!2016/06/06
! -(done) Move market clearing to its own function
!2016/06/07
! -(done) In DP, add ProbDeath to value function calculation
! -(done) In Simulate: initialize AgeInd to realistic distribution, change updating of AgeIndNext, change calculation of NumRetired
! -(done) Got rid of outputWelfAge, TempArrayI_nAge, temp02.txt. Everything about agents is now stored in outputWelf
! -(done) Changed temp01.txt and temp03.txt to output00.m and output01.m
! -(done) Checked that if set ProbDeath=[0 0 ... 1] and everything else same as old code, then results are the same (other than randomness)
! -(done) In Clearmarkets multiplied Pension by Zind(i), changed input/output so that Pension is passed to Simulate
! -(done) In Beliefs, changed so that Pension is regressed on Wage
!2016/06/12
! -(done) Declare nAgent as parameter in main, pass it to DP and Simulate, declare in OpenMP in Simulate
! -(done) Add sort subroutine
! -(done) Create subroutine InitAgeInd which simulates long time series. Its outputs are AgeInd (written to AgeInt.txt), NumRetired (passed to DP to compute Pension), NumDeadR,NumDeadW (passed to Simulate to reduce effect of idiosyncratic randomness due to death)
! -(done) Replace initialization of AgeIndNext in Simulate by reading AgeInt.txt
! -(done) In DP change calculation of PensionGrid. Where Price is being calculated, replace it by Wage*HoursDemand/NumRetired, where HoursDemand can be computed from from firm's equilibrium conditions if we know (Wage,PH1,PH2)
! -(done) Change all references to 8 regressions, it is now 7 because PensionGrid comes from equilibrium
! -(done) In Simulate: create DeathShock, sort it separately for workers and retirees to determine cutoffs for each (using NumDeadR and NumDeadW), then determine who dies
! -(done) In main part of DP tax was declared private but should have been shared in OpenMP, now fixed
! -(done) In InitAgeInd, got rid of parallelization - was causing randomness in NumDead
! -(done) In older code, the retired believe their productivity is A(t+1)=A(t)*dZ(2), however this is a problem when dZ(2)~=1. Fixed by introducing variable Normalize
! -This version works well, however the young start out with too much wealth. To fix this need agents to
!  receive bequests later in life. Because this version has permanent income shocks, this version does not
!  allow agents to recieve bequests later in life. Thus, next will switch to stationary shocks
!2016/06/14
! -(done) In DP: when skipping certain iDZnext for retired, change iDZnext.ne.2 to iDZnext.ne.iDZ
! -(done) In DP: replace certain references to DZgrid by Normalize, where Normalize=1
! -(done) In DP: add DZgrid to LaborIncome calculation
! -(done) In DP: create iInd=(iDZ-1)*nNW+iNW and iIndNext. Use it when creating ValFunNext and using iStateNextL to call ValFunNext
! -(done) pass iZind to ClearMarkets from Simulate, and to GetPolicy from ClearMarkets. Use iInd=(iZind-1)*nNW+iNW when calling on poliyc and value arrays
! -(done) In GetPolicy: Do not normalize NW by Zind at start, do not multiply Zind and Hind by Zind at end
! -(done) In Simulate: Change TrProbDZ(nDZ) to TrProbDZ(nDZ,nDZ), same for TrProbDZcum
! -(done) Add coe to compute unconditional distribution of dZ and start agents iZindNext w/ unconditional
! -(done) Replace code for computing ZindNext by iZindNext, set Zind=DZgrid(iDZ)
! -(done) Changed how tiebreaker applies - only applies when difference b/w 1st and 2nd best in Vcond is very small
! -(done) Added 0.0001*real(mod(i-1,11)+1-6) to reporting of Zind in outputWelf
! -(done) Changed market clearing: a) mod(iClMkt,100) to mod(iClMkt,50), b) initial prices come from regression rather than previous prices
! -(done) Changes initial iZind for those of AgeInd=1 so that it comes from unconditional distribution. Otherwise those w/ high iZind parents receive both higher iZind and higher bequest
! -(done) NumRetired changed to real
! -(done) nRegr changed to 8 (belief about bequest). In Beliefs added code to compute 8th regression. In Simulate restricting outcome of this by min and max
! -(done) In InitAgeInd change the random calculation of NumDead to analytic, checked that its correct. Add calculation of BeqProb
! -(done) In Simulate add BequestExp=Sum(ProbDeath*NWnext) as opposed to Bequest, which has Avg[NWnext|dead]. Using this BequestExp instead of Bequest in Simulate to compute beliefs and inheritance amount.
! -(done) In DP added possibility of receiving bequest: NWnext and NWnextBeq. Now calling CHFIV twice
! -(done) In Simulate computing Bbeq, HObeq, HIbeq and passing them to clearmarkets, where they are given to agents w/ BeqReceiver=1
! -(done) In both DP and
! -(done) Changed PensionIncome to (0.5+0.5*Z)*Pension from just Z*Pension in boht DP and ClearMarkets
! -(done) In DP: for retired (iAge<=nRet) a) allow Hours>0, b) LaborIncome=AgeProd*Z*Wage*(1-tax)+PensionIncome. In ClearMarkets: for retired (iAge>nAge-nRet) a) allow Hours>0, b) LaborIncome=AgeProd*Z*Wage*(1-tax)+PensionIncome, c) PensionTax collected for anyone with HoursInd>0, instead of iAge<=nAge-nRet
! -(done) Changed computation of NumRetired in Simulate to include only AgeInd(i).gt.nAge-nRet

!2016/08/02
! -(done) In writedata1 now writing various parameters so that no need to hardcode them when computing moments in matlab
! -(done) Changed HFgrid(iHF) to HFgrid(iHF,iLOC). Added HFVgrid which measures which fraction of foreign owned housing is left vacant to locals (either actually vacant or foreigners live there). 1-HFVgrid can be rented out. This goes into market clearing conditions
! -(done) Added parameter LeisureMin to wherever CommCost was, changed CommCost(iLOC) to CommCost(iLOC,:) where 2nd dimension has size 2, is for cost when working (1) versus retires (2)
! -(done) Before, CommCost(iLOC,1) was applied to everyone. Fixed this so that CommCost(iLOC,2) applies to retired or those with Hours=0, CommCost(iLOC,1) applies to everyone else

!2016/08/19
! -(done) Created getpolicy0, which speeds things up by interpolating over NW last. The other dimensions reuse previously done calculations
! -(done) Added taxprop. If (i) set taxprop=depr(OldCode)-depr(NewCode), (ii) set PropTaxRedist=0, (iii) when updating H in clearmarkets use (1-depr-taxprop) instead of (1-depr) then results identical to old code
! -(done) Added HresMin
! -(done) Added CluxCost and CluxCut

!2016/09/03
! - Adding rent control. nRC=0 if no rent control and nRC=1 if rent control
! -(done) Changed size of 2nd dimension of policy,ValFunCond,TieBreaker from 2x (renter,owner) to (2+nRC)x (renter,owner,rent controlled renter)
!  -This also includes reading and writing those functions

!2016/11/02
! -Added NWgridAll so that an agent's NWgrid is now conditional on (iAge,iDZ). This allows us to have finer grid with a low nNW
! -To make code identical to old code, make NWgridAll be same as NWgrid, and not condition on (iAge,iDZ)
!  -To do this, a) comment out any references to makenwgrid; b) write NWgrid.txt at the start of code

! -In Simulate not including the collateral constraint as in DP. In principle it should not matter because optimal policy takes account of constraint. However should later check that constraint is not violated
! -When calibration gets better must experiment w/ tiebreaker. If enough diversity, is TieBreaker=0 ok? Can we get away w/ a smaller TieBreaker when nAgent is bigger? Currently can't test this because high nAgent --> Wage is below grid
! -In DP, Hchoice=0 when RP=0. Need to check that this is optimal (if housing is a good enough hedge, there may be demand for investment property at zero or even negative risk premiums). Can check this by expeding RPgrid to have negative values
! -Need to check that in Simulate, once everything has converged, PensionBelief=Pension

!2018/12/06
! -Added persistent RC. To use:
!  -For non-persistent RC set nRClast=1 and uncomment below lines 2758 and 8210 (last part doesn't actually matter but might as well)
!   OR set nRClast=nLOC+1 and uncomment below lines 2758 and 8210
!  -For persistent RC set nRClast=nLOC+1 and comment out below lines 2758 and 8210

!2019/04/02
! -Made changes to how persistence works. In particular, added variables flagRCstay and RCprobTemp to DP and Clearmarkets. I think (but not 100% sure) this doesn't end up changing any of the output 
!  for the case with no persistence (nRC=1), the case with persistence (nRC=3). However, it fixes the case with no persistence (nRC=3) to be consistent with no persistence (nRC=1).
! -In choosing RCreceiver(i), changed .lt. to .le. and .ge. to .gt. --> I think this is more consistent w/ how we set RCprob, however should make small difference since it just shifts 1 agent into RC
! -Towards the end of DP added: ValFunCond(iState,(2+nRC)*nLOC+1)=ValFun0(iState,1), this doesn't affect output but makes it easier to diagnose errors when fixing bugs. Also simplified
!  the section around valXX.dat to reflect the change to ValFunCond

      program ModelOfCity
      implicit none
      integer nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nAgg,nLOC,i
      integer nDZ,nRet,nAge,j,mytime(3),flagWelf,nRegr,nInd,nRC,iHF
      integer tempI1,tempI2,tempI3,tempI4
      integer nAgent,nAgent0,TotYears,nDepr,nBeqDist,nRClast
      real NWmin,NWmax
      parameter(nWage=4,nRent1=4,nRent2=4,nRP1=2,nRP2=2,nH1=3,nH2=3)
      parameter(nNW=57,nHF=2,nLOC=2,nDZ=6,nDepr=1,nRC=0)  !Baseline model: nDZ=6; NYC: nDZ=8; VAN: nDZ=8
      parameter(nAge=20,nRet=9,nRegr=13)    !iRegression: 1=Wage, 2=Rent1, 3=Rent2, 4=PR1, 5=PR2, 6=H1, 7=H2, 8=Bequest, 9=RentControlled(1)/AllRented(1), 10=RentControlled(2)/AllRented(2), 11=ShareOwned(1), 12=ShareOwned(2), 13, Pension
      parameter(nAgent=2000,nAgent0=500,TotYears=2000)
      parameter(NWmin=0.0,NWmax=25.0,nBeqDist=3)
      parameter(nRClast=1) !nRClast=1 when no persistent RC and nRClast=3 when persistent RC
      real nFirmC,nFirm1,nFirm2
      integer flagRCstay(nHF)
      double precision TrProbDZ0(nDZ,nDZ),TrProbDZ1(nDZ,nDZ)
      double precision TrProbDZ2(nDZ,nDZ)
      double precision UncondDist0(1,nDZ),UncondDist1(1,nDZ)
      real TrProbDZuncond(nDZ,nDZ),UncondDistDZ(1,nDZ)
      real output(TotYears,50),outputWelf(TotYears*nAgent0,15)
      real outputErr(TotYears,7)
      real PriceBond,thetaRes,thetaInv,beta0,gamma0,alphaN,alphaC,alphaH
      real ElastCH,ElastCN,chi0,HoursMin
      real lambda0(nHF),tau0(nHF),lambdaBase,tauBase
      real deprH(nLOC),deprINV0,taxss,taxprop(nHF,nLOC),taxpropOOT(nLOC)
      real HresMin,DeathExp
      real RTSC,RTSH0loc1,HBARloc1(nHF),RTSH0loc2,HBARloc2(nHF)
      real WageGrid(nWage),Rent1Grid(nRent1),Rent2Grid(nRent2)
      real RP1grid(nRP1),RP2grid(nRP2),DZgrid(nAge,nDZ),DZgridAvg(nDZ)
      real NWgrid(nNW),NWgridAll(nAge*nDZ,nNW)
      real H1grid(nH1),H2grid(nH2),HFVgrid(nHF,nLOC)
      real HFgrid0(nHF,nLOC),HFgrid1(nHF,nLOC)
      real TrProbHF(nHF,nHF),TrProbDZ(nDZ,nDZ)
      real CommCost(nLOC,2),CommCostFin(nLOC,2),LeisureMin
      real AgeProd(nAge),CluxCut(2),CluxCost(2),ProfitRedist(3)
      real Regcoefs1(nRegr,nHF*nHF),Regcoefs2(nRegr,nHF*nHF)
      real Regcoefs3(nRegr,nHF*nHF),Regcoefs4(nRegr,nHF*nHF)
      real Regcoefs5(nRegr,nHF*nHF),Regcoefs6(nRegr,nHF*nHF)
      real Regcoefs7(nRegr,nHF*nHF),Regcoefs0(nRegr,nHF*nHF)
      real Regcoefs8(nRegr,nHF*nHF),Regcoefs9(nRegr,nHF*nHF)
      real Regcoefs10(nRegr,nHF*nHF),Regcoefs11(nRegr,nHF*nHF)
      real RegcoefsMin(nRegr,nHF*nHF),RegcoefsMax(nRegr,nHF*nHF)
      real RegcoefsBeq0(2*nBeqDist,nHF*nHF)
      real RegcoefsBeq1(2*nBeqDist,nHF*nHF)
      real RegcoefsBeqMin(2*nBeqDist,nHF*nHF)
      real RegcoefsBeqMax(2*nBeqDist,nHF*nHF)
      real NumDeadR,NumDeadW,NumRetired,SSIdist(nDZ)
      real RCinccut(nLOC,nHF),RChsize(nLOC,nHF)
      real RCrentred(nLOC,nHF),RCshare(nLOC,nHF)
      real Z1shiftSize(2),Z1shiftCut(2),Z1shiftAll
      real popShare1,rentDiff,incDiff,AvgHomeRenter(nLOC)
      real AvgIncome,AvgIncomeWorker,MedIncomeWorker
      real RCshareRent(nLOC,nHF),Rent(nLOC),Hres(nLOC)
      real tempR1,tempR2,tempR3,tempR4,tempR5
      real NWbound(nAge*nDZ,2),kappa2,kappa3
      real fracBeq,BeqStrength(nDZ),BeqLux(nDZ),NumBorn
      real DeprGrid(nDepr),DeprProb(nDepr),BetaRel(nDZ)
      real fracRet(nLOC),PubGood,RCshareAll(nLOC,nHF)
      real RCprobStay(nLOC),fracSameRC,RCsubs(nLOC,nHF)

      nAgg=nWage*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF
      nInd=nNW*nDZ*nRClast

!Create initial AgeInd distribution for simulate and compute number of retired and dead households
      call InitAgeInd(nAgent,nAge,nRet,NumDeadR,NumDeadW,NumRetired,
     1                NumBorn)
!Baseline, NYC, and VAN models all have different DZgrid.txt
      call readdata(DZgrid,'DZgrid.txt',nAge,nDZ,nAge,nDZ)
      do j=1,nDZ
       tempR1=0
       do i=1,nAge-nRet
        tempR1=tempR1+DZgrid(i,j)
       end do
       DZgridAvg(j)=tempR1/real(nAge-nRet)
      end do
      do i=1,nAge
       write(6,'(f9.4,f9.4,f9.4,f9.4,f9.4,f9.4,f9.4,f9.4)')
     1  (DZgrid(i,j),j=1,nDZ)
      end do

      fracBeq=0.25
      do i=1,nDZ/2
       BeqStrength(i)=0.0
       BeqStrength((nDZ/2)+i)=0.0
       BeqLux(i)=0.0
       BeqLux((nDZ/2)+i)=0.0
       BetaRel(i)=0.93333333
       BetaRel((nDZ/2)+i)=1.20
      end do

      do i=1,nDZ
      do j=1,nDZ
       TrProbDZ(i,j)=0
      end do
      end do

!     Baseline Model
      TrProbDZ(1,1)=0.9299
      TrProbDZ(1,2)=0.0701
      TrProbDZ(2,1)=0.0392
      TrProbDZ(2,2)=0.9216
      TrProbDZ(2,3)=0.0392
      TrProbDZ(3,2)=0.1802
      TrProbDZ(3,3)=0.8198
      TrProbDZ(4,4)=0.85
      TrProbDZ(4,5)=0.15
      TrProbDZ(5,4)=0.025
      TrProbDZ(5,5)=0.875
      TrProbDZ(5,6)=0.100
      TrProbDZ(6,5)=0.050
      TrProbDZ(6,6)=0.950
!     NYC Model
!      TrProbDZ(1,1)=0.9299
!      TrProbDZ(1,2)=0.0701
!      TrProbDZ(2,1)=0.0392
!      TrProbDZ(2,2)=0.9216
!      TrProbDZ(2,3)=0.0392
!      TrProbDZ(3,2)=0.0392
!      TrProbDZ(3,3)=0.9216
!      TrProbDZ(3,4)=0.0392
!      TrProbDZ(4,3)=0.1802
!      TrProbDZ(4,4)=0.8198
!      TrProbDZ(5,5)=0.85
!      TrProbDZ(5,6)=0.15
!      TrProbDZ(6,5)=0.025
!      TrProbDZ(6,6)=0.875
!      TrProbDZ(6,7)=0.100
!      TrProbDZ(7,6)=0.025
!      TrProbDZ(7,7)=0.875
!      TrProbDZ(7,8)=0.100
!      TrProbDZ(8,7)=0.050
!      TrProbDZ(8,8)=0.950
!     VAN Model
!      TrProbDZ(1,1)=0.9070
!      TrProbDZ(1,2)=0.0930
!      TrProbDZ(2,1)=0.0977
!      TrProbDZ(2,2)=0.8046
!      TrProbDZ(2,3)=0.0977
!      TrProbDZ(3,2)=0.1083
!      TrProbDZ(3,3)=0.7834
!      TrProbDZ(3,4)=0.1083
!      TrProbDZ(4,3)=0.3104
!      TrProbDZ(4,4)=0.6896
!      TrProbDZ(5,5)=0.9070
!      TrProbDZ(5,6)=0.0930
!      TrProbDZ(6,5)=0.0977
!      TrProbDZ(6,6)=0.8046
!      TrProbDZ(6,7)=0.0977
!      TrProbDZ(7,6)=0.1083
!      TrProbDZ(7,7)=0.7834
!      TrProbDZ(7,8)=0.1083
!      TrProbDZ(8,7)=0.1300
!      TrProbDZ(8,8)=0.8700

!      if(fracBeq.gt.0.00001) then
!       do i=1,(nDZ/2)
!!       DZgrid(i+(nDZ/2))=DZgrid(i)
!        do j=1,(nDZ/2)
!         TrProbDZ(i+(nDZ/2),j+(nDZ/2))=TrProbDZ(i,j)
!        end do
!       end do
!      end if
      DeprGrid(1)=1.0
      !DeprGrid(2)=1.0
      DeprProb(1)=1.0!0.5
      !DeprProb(2)=0.5


!compute the unconditional distribution of households
      do i=1,nDZ
      do j=1,nDZ
       if(fracBeq.lt.0.00001) then
        UncondDist0(1,i)=1.0/real(nDZ)
       else
        if(i.le.nDZ/2) then
         UncondDist0(1,i)=2.0*(1.0-fracBeq)/real(nDZ)  !For 100% non-bequesters this should be 2.0, for 10% non-bequesters this should be 1.8
        else
         UncondDist0(1,i)=2.0*fracBeq/real(nDZ)  !For 100% non-bequesters this should be 0.0, for 10% non-bequesters this should be 0.2
        end if
       end if
       TrProbDZ0(i,j)=TrProbDZ(i,j)
       TrProbDZ1(i,j)=TrProbDZ(i,j)
       TrProbDZ2(i,j)=TrProbDZ(i,j)
      end do
      end do
      do tempI1=1,200
       call matmult(TrProbDZ0,TrProbDZ1,TrProbDZ2,nDZ,nDZ,nDZ)
       do i=1,nDZ
       do j=1,nDZ
        TrProbDZ1(i,j)=TrProbDZ2(i,j)
        TrProbDZuncond(i,j)=real(TrProbDZ2(i,j))
       end do
       end do
      end do
      call matmult(UncondDist0,TrProbDZ2,UncondDist1,1,nDZ,nDZ)
      do i=1,nDZ
       UncondDistDZ(1,i)=UncondDist1(1,i)
      end do

      do i=1,nDZ
      write(6,'(f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4)')
     1 (TrProbDZ(i,j),j=1,nDZ)
      end do
      do i=1,nDZ
      write(6,'(f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4)')
     1 (TrProbDZuncond(i,j),j=1,nDZ)
      end do
      write(6,'(f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4)')
     1 (UncondDistDZ(1,j),j=1,nDZ)


!compute the social security tax, in dollar terms, that each household would receive

      tempR1=66406 !Average household labor inomce in 2010 for US
!      tempR1=92000 !Average household labor income in 2016 for NYC
!      tempR1=97878 !Average household labor income in 2016 for VAN (not needed for code)
!the loop below is done for Baseline or NYC models, comment out for VAN
      tempR3=0
      do i=1,nDZ
       tempR2=tempR1*dZgridAvg(i) !average income of current group
       if(tempR2.le.791*12) SSIdist(i)=tempR2*12*0.9
       if(tempR2.gt.791*12.and.tempR2.le.4781*12) then
        SSIdist(i)=791*12*0.9+(tempR2-791*12)*0.32
       end if
       if(tempR2.gt.4781*12.and.tempR2.le.117500) then
        SSIdist(i)=791*12*0.9+4781*12*0.32+(tempR2-4781*12)*0.15
       end if
       if(tempR2.gt.117500) then
        SSIdist(i)=791*12*0.9+4781*12*0.32+(117500-4781*12)*0.15
       end if
       tempR3=tempR3+SSIdist(i)*real(UncondDist1(1,i))
      end do

!Canada pension explanation:
! 1) Old Age Security (OAS) guaranteed pension
!    -Basic pension amount $6.8K/year to every household (households with post-retirement income above $71.6K receive reduced OAS, but very few retired households have such high income)
!    -Funded by federal gov't general budget. In 2016-2017 $48.3B went to OAS, from a total of $143.2B personal taxes collected -> 34% of personal taxes
!    -The average personal tax rate in Canada was 12%, so 4% of personal income was used to fund OAS. To compute 12% average tax rate, I needed average household income. For this use http://www.statcan.gc.ca/tables-tableaux/sum-som/l01/cst01/famil105a-eng.htm get number of individuals in each income group p and income of each group w (I used midpoint, and 1.5x$250K for top group). This gives sum(p.*w)=$1.19T total personal income. $143B personal tax / $1.19T personal income = 12%. For average personal income, divide $1.19B by 35.5M population and multiply by 2.5 household size to get $85.6K average household income in 2014. Compare this to $78.9K median in 2014 http://www.statcan.gc.ca/tables-tableaux/sum-som/l01/cst01/famil107a-eng.htm
!    -Note that 4% is the average tax, however federal taxes are progressive so high earners pay more than 4% and low earners less than 4%
! 2) Canada Pension Plan (CPP) pay-as-you go system which works like U.S. social security
!    -Workers receive 25% of earnings on which contributions were made, up to 13K per year  (average Canadian receives 6.5K)
!    -The earnings are defined (approximately) as average lifetime earnings
!    -Contributions are 9% (half from employee, half from employer) on earnings up to 51.1K  (average Canadian income 50K -> pays 4.5K)
!    -From same data I used to compute average income, I can compute the fraction of all income taxed at 9%: sum(min(w,53).*p)/sum(p.*w)=72.7%
!    -This implies that the the average tax paid was 9%*0.727=6.5%
!    -Note that 6.6% is the average tax, however this tax is regressive so high earners pay less than 6.5% and low earners pay more than 6.5%
! Total tax: on average 4% for OAS (progressive) 6.5% for CPP (regressive) --> lets say 10.5% flat?
! To compute distribution by group:
! Avg Vancouvere income: 97878 --> 6.8K from OAS and min(0.25*97.878K,13K)=13K from CPP --> 19.8K total
! Group 1: income 0.250*97.878K=24.47K  --> 6.8K from OAS and 6.1K from CPP --> 12.1K total
! Group 2: income 0.704*97.878K=68.91K  --> 6.8K from OAS and 13K from CPP --> 19.8K total
! Group 3: income 1.308*97.878K=128.02K --> 6.8K from OAS and 13K from CPP --> 19.8K total
! Group 4: income 2.946*97.878K=288.35K --> 6.8K from OAS and 13K from CPP --> 19.8K total

!the loop below is done for VAN model, comment out for NYC and baseline
!      tempR3=0
!      do i=1,nDZ
!       SSIdist(i)=12.1
!       if(mod(i,nDZ/2).ne.1) SSIdist(i)=19.8
!       tempR3=tempR3+SSIdist(i)*real(UncondDist1(1,i))
!      end do

!The loop below is done for all cases
      do i=1,nDZ
       SSIdist(i)=SSIdist(i)/tempR3
       write(6,'(i4,f8.4,f8.4)') i,real(UncondDist1(1,i)),SSIdist(i)
      end do

!ForeignDemandPerDomesticHousehold = exp{HFgrid0-HFgrid1*log(Price)}
      HFgrid0(1,1)=-10000.0   !low state,  zone 1: constant (in logs)
      HFgrid0(2,1)=log(0.0068) !high state, zone 1: constant (in logs)
      HFgrid0(1,2)=-10000.0   !low state,  zone 2: constant (in logs)
      HFgrid0(2,2)=log(0.0148) !high state, zone 2: constant (in logs)
      HFgrid1(1,1)=0.0        !low state,  zone 1: intercept
      HFgrid1(2,1)=0.6        !high state, zone 1: intercept
      HFgrid1(1,2)=0.0        !low state,  zone 2: intercept
      HFgrid1(2,2)=0.6        !high state, zone 2: intercept
!This is the fraction of propertis owned by foreigners that are kept vacant. 1-HFVgrid is the fraction they rent out to locals
      HFVgrid(1,1)=1.00 !low state,  zone 1
      HFVgrid(2,1)=1.00 !high state, zone 1
      HFVgrid(1,2)=1.00 !low state,  zone 2
      HFVgrid(2,2)=1.00 !high state, zone 2
      TrProbHF(1,1)=0.9
      TrProbHF(2,1)=0.1
      TrProbHF(1,2)=0.1
      TrProbHF(2,2)=0.9

      LeisureMin=0.00
      CommCost(1,1)=0.00 !zone 1, worker
      CommCost(2,1)=0.0359 !zone 2, worker
      CommCost(1,2)=0.00 !zone 1, non-worker
      CommCost(2,2)=CommCost(2,1)/3.0 !zone 2, non-worker
      CommCostFin(1,1)=0.000
      CommCostFin(2,1)=0.033*0.285
      CommCostFin(1,2)=0.000
      CommCostFin(2,2)=CommCostFin(2,1)/3.0

      DeathExp=0.0            !20% of estate value
      HresMin=0.25
      PriceBond=0.825
      thetaRes=0.90
      thetaInv=0.90
      beta0=0.85
      gamma0=5.0
      alphaN=0.68 !NYC: 31.5%, OOT: 30.8% of non-sleep hours spent on working
      alphaH=0.26 !NYC: Avg[Rent*H]/Avg[IncomeWorker]=23.0%. OOT: 21.6% of expenditures spent on housing
      alphaC=1.0-alphaH !1/3 of expenditures spent on housing
      ElastCH=-0.5
      ElastCN=0.0
      chi0=1.0
!The different lambda's and tau's matter for the voucher experiment only. For everything else labmda(1)=lambda(2)=lambdaBase and tau(1)=tau(2)=tauBase
!For the voucher experiment there are two ways of doing it:
!1) Regime switch from no vouchers (1) to vouchers (2). In this case:
!  -set lambda0(2)<lambda0(1) (more progressive) and set tau0(2) s.t. total gov't surplus is equal to 1
!  -set lambdaBase=lambda0(1) and tauBase=tau0(1), this is used to compute how much of the transfer is used for the voucher
!2) No regime switch, just compare across models. In this case:
!  -set lambda0(2)=lambda0(1) to be lower (more progressive) than in the baseline model
!  -set tau0(2)=tau0(1) to have the same gov't surplus as in the baseline model
!  -set lambdaBase and tauBase to be their values in the baseline model (not equal to lambda0 or tau0), this is used to compute how much of the transfer is used for the voucher
      lambda0(1)=1.0
      lambda0(2)=1.0
      lambdaBase=1.0
      tau0(1)=0.0
      tau0(2)=0.0
      tauBase=0.0
      HoursMin=0.15
      CluxCut(1)=100.0  !Consumption below which cost of consumption is identical in Zone1 and Zone2
      CluxCut(2)=100.0  !Consumption below which cost of consumption is identical in Zone1 and Zone2
      CluxCost(1)=0.0 !Additional cost of consumption if C>CluxCut and living in Zone2
      CluxCost(2)=0.0 !Additional cost of consumption if C>CluxCut and living in Zone2
      Z1shiftAll=0.92992  !Additional utility (1.0 is no addition) for being in Zone 1 for any household
      Z1shiftCut(1)=0.25  !Consumption below which utility is identical in Zone1 and Zone2, workers
      Z1shiftCut(2)=0.0  !Consumption below which utility is identical in Zone1 and Zone2, retirees
      Z1shiftSize(1)=1.03124   !Additional utility (1.0 is no addition) for being in Zone1 if C>Z1shiftCut, workers
      Z1shiftSize(2)=1.05404   !Additional utility (1.0 is no addition) for being in Zone1 if C>Z1shiftCut, retirees
      deprH(1)=0.09457
      deprH(2)=0.09457+0.0000
      deprINV0=0.0
      taxss=0.10      !10% for baseline and NYC models, 10.5% for Vancouver
      taxprop(1,1)=0.063   !Property tax in low OOT state, Zone 1
      taxprop(2,1)=0.063   !Property tax in high OOT state, Zone 1. State dependent only for experiment where tax goes down in high OOT state to keep total revenue same
      taxprop(1,2)=0.063   !Property tax in low OOT state, Zone 2
      taxprop(2,2)=0.063   !Property tax in high OOT state, Zone 2. State dependent only for experiment where tax goes down in high OOT state to keep total revenue same
      taxpropOOT(1)=0.063     !tax on foreign owners of property (this is not a surcharge, this is the actual tax so should be at least as high as taxprop)
      taxpropOOT(2)=0.063
      PubGood=1.15      !weight on public good in utility function
      RTSC=0.66                !return to scale parameter in production of consumption good
      RTSH0loc2=0.66           !1st return to scale parameter in production of housing good in location 2
      HBARloc2(1)=3.3        !2nd return to scale parameter in production of housing good in location 2
      HBARloc2(2)=3.3
      RTSH0loc1=0.66           !1st return to scale parameter in production of housing good in location 1
      HBARloc1(1)=0.21645!HBARloc2(1)*0.0312    !2nd return to scale parameter in production of housing good in location 1, NYC: 0.0238*HBARloc2, VAN: 0.061*HBARloc2
      HBARloc1(2)=0.21645!HBARloc2(2)*0.0312
      ProfitRedist(1)=0     !fraction of C profits that stays in city
      ProfitRedist(2)=0     !fraction of H1 profits that stays in city
      ProfitRedist(3)=0     !fraction of H2 profits that stays in city
      nFirmC=real(nAgent)
      nFirm1=real(nAgent)
      nFirm2=real(nAgent)

!consumption sector:
!each firm's output: HoursC^RTSC
!each firm's labor demand: HoursC=(RTSC/Wage)^(1/(1-RTSC))
!each firm's output as function of wage: (RTSC/Wage)^(RTSC/(1-RTSC))
!aggregate labor demand by sector: nFirm*(RTSC/Wage)^(1/(1-RTSC))
!aggregate output:  C=nFirm*(RTSC/Wage)^(RTSC/(1-RTSC))
!housing sector:
!each firm's output: x*HoursH^RTSH where RTSH=RTSH0 and x=1-H/HBAR
!each firm's labor demand: HoursH=(x*PH*RTSH/Wage)^(1/(1-RTSH))
!each firm's output as a function of wage: (x^(1/(1-RTSH))) * (PH*RTSH/Wage)^(RTSH/(1-RTSH))
!aggregate labor demand by sector: nFirm*(x*PH*RTSH/Wage)^(1/(1-RTSH))
!aggregate output by sector: Hnext-(1-d)*H=nFirm * (x^(1/(1-RTSH))) * ((PH*RTSH/Wage)^(RTSH/(1-RTSH)))
!if nFirm is proportional to nAgent (for simplicity normalize nFirm=nAgent) and if H0 is proportional to nAgent, then equilibrium is invariant to nAgent

!rent control parameters (if no rent control set nRC=0 or RCshare=0

!Baseline:
!RCinccut(1)=RCinccut(2)=0
!RChsize(1)=RChsize(2)=0
!RCshare(1)=RCshare(2)=0
!RCrentred(1)=RCrentred(2)=0
!NYC:
!RCinccut(1)=RCinccut(2) should be roughly 200% of avg income (avg income of rent controlled in NYC is 65% of non-rent controlled)
!RCshare(1)=0.2148 and RCshare(2)=0.1329. These are shares of all square feet that are rent control, in order to match 0.169 and 0.104 fraction of all rental units that are rent controlled
!RCrentred(1)=RCrentred(2)=0.5. This is the discount relative to market rent
!RChsize(1)=RChsize(2)=0.1*RCinccut should be roughly 20% of average income. This is the maximum rent that can be paid for a rent controlled apartment
!VAN
!RCinccut(1)=RCinccut(2) should be 53% (52k limit and 98.78 avg)
!RCshare(1)=?? and RCshare(2)=??. These are shares of all square feet that are rent control, in order to match 0.173 and 0.158 fraction of all rental units that are rent controlled
!RCrentred(1)=RCrentred(2)=0.47. This is the discount relative to market rent
!RChsize(1)=RChsize(2)=0.1*RCinccut we don't know the right number to use, so just using the one for NYC
      MedIncomeWorker=0.292 !medium income
      kappa2=0.01
      kappa3=0.01
      RCinccut(1,1)=MedIncomeWorker*kappa2             !maximum income to qualify for rent control
      RCinccut(2,1)=RCinccut(1,1)            !maximum income to qualify for rent control
      RCinccut(1,2)=RCinccut(1,1)
      RCinccut(2,2)=RCinccut(1,1)
      RChsize(1,1)=MedIncomeWorker*kappa3  !maximum rent of a rent controlled apartment: (1-RCrentred)*Rent*H < RCHsize = AMI*0.64
      RChsize(2,1)=MedIncomeWorker*kappa3
      RChsize(1,2)=MedIncomeWorker*kappa3
      RChsize(2,2)=MedIncomeWorker*kappa3
      RCrentred(1,1)=0.0 !Average discount for regulated units
      RCrentred(2,1)=0.0 !Average discount for regulated units
      RCrentred(1,2)=0.0
      RCrentred(2,2)=0.0
      RCshare(1,1)=0.0  !Share of all square feet that are rent controlled
      RCshare(2,1)=0.0  !Share of all square feet that are rent controlled
      RCshare(1,2)=0.0
      RCshare(2,2)=0.0
      RCprobStay(1)=0.5
      RCprobStay(2)=0.5
      RCsubs(1,1)=0.0!0.125!0.0 !--> targeted such that 30% of total construction costs (wage bill) for RC housing is covered by subsidies
      RCsubs(2,1)=0.0!0.125!0.0
      RCsubs(1,2)=0.0!0.125!0.0
      RCsubs(2,2)=0.0!0.125!0.0
      flagRCstay(1)=0  !1=persistence in stying in RC, 0=no persistence. Note that when nRClast=1 then value of flagRCstay doesn't matter, but when nRClast>1 then need to set flagRCstay=0
      flagRCstay(2)=0

      WageGrid(1)=1.075
      WageGrid(2)=1.100
      WageGrid(3)=1.125
      WageGrid(4)=1.150

      Rent1Grid(1)=0.08
      Rent1Grid(2)=0.12!Rent1Grid(1)+0.06
      Rent1Grid(3)=0.15!Rent1Grid(1)+0.12
      Rent1Grid(4)=0.19!Rent1Grid(1)+0.18
      Rent2Grid(1)=0.08
      Rent2Grid(2)=0.12!Rent2Grid(1)+0.05
      Rent2Grid(3)=0.15!Rent2Grid(1)+0.10
      Rent2Grid(4)=0.19!Rent2Grid(1)+0.15

      RP1grid(1)=0.0000
      RP1grid(2)=0.0050
      !RP1grid(3)=0.005

      RP2grid(1)=0.0000
      RP2grid(2)=0.0050
      !RP2grid(3)=0.005

      H1grid(1)=0.09
      H1grid(2)=0.11
      H1grid(3)=0.13
      H2grid(1)=0.43
      H2grid(2)=0.47
      H2grid(3)=0.51

!      NWgrid(1)=0.000
!      NWgrid(2)=0.001
!      NWgrid(3)=0.010
!      NWgrid(4)=0.025
!      NWgrid(5)=0.045
!      NWgrid(6)=0.070
!      NWgrid(7)=0.100
!      NWgrid(8)=0.140
!      NWgrid(9)=0.200
!      do i=10,nNW
!       NWgrid(i)=NWgrid(i-1)+(NWgrid(i-1)-NWgrid(i-2))*1.05
!      end do



!      tempR1=NWmax!NWbound(i,2)*1.5
!      if(tempR1.lt.0.5) tempR1=0.5
!      if(tempR1.ge.0.9*NWmax) tempR1=0.9*NWmax
!      tempR2=(tempR1-NWmin)*0.1/((1.1**real(nNW-2))-1.0)
!      NWgrid(1)=NWmin
!      do j=2,nNW-1
!       NWgrid(j)=NWgrid(j-1)+tempR2*(1.1**real(j-2))
!!       write(6,*) j,NWgrid(j)
!      end do
!      NWgrid(nNW)=NWmax


      tempR1=NWmax!NWbound(i,2)*1.5
      if(tempR1.lt.0.5) tempR1=0.5
      if(tempR1.ge.0.9*NWmax) tempR1=0.9*NWmax
!!this loop finds x s.t. NWgrid(1)=0, NWgrid(2)=0.01, NWgrid(i)=(NWgrid(i-1)-NWgrid(i-2))*(1+x), NWgrid(nNW-1)=0.9*NWmax
      tempR4=10000.0
      do j=1,200
       tempR2=0.25*real(j)/200.0
       tempR3=abs(tempR1-NWmin-
     1       0.01*(((1.0+tempR2)**real(nNW-2))-1.0)/tempR2)
       if(tempR3.lt.tempR4) then
        tempR5=tempR2
        tempR4=tempR3
       end if
      end do
      NWgrid(1)=NWmin
      do j=2,nNW-1
       NWgrid(j)=NWgrid(j-1)+0.01*((1.0+tempR5)**real(j-2))
!       write(6,*) j,tempR5,NWgrid(j)
      end do
      NWgrid(nNW)=NWmax

      do i=1,nAge*nDZ
       NWbound(i,1)=NWgrid(1)
       NWbound(i,2)=NWgrid(nNW)
       do j=1,nNW
        NWgridAll(i,j)=NWgrid(j)
       end do
      end do
      !call writedata(NWbound,'NWbnd0.txt',nDZ*nAge,2,nDZ*nAge,2)

      do i=1,nAge
       AgeProd=1.0
      end do

      AgeProd(1)=0.4088
      AgeProd(2)=0.6375
      AgeProd(3)=0.8236
      AgeProd(4)=0.9262
      AgeProd(5)=1.0139
      AgeProd(6)=1.1078
      AgeProd(7)=1.1771
      AgeProd(8)=1.2848
      AgeProd(9)=1.2481
      AgeProd(10)=1.2298
      AgeProd(11)=1.1425
      AgeProd(12)=0.01
      AgeProd(13)=0.01
      AgeProd(14)=0.01
      AgeProd(15)=0.01
      AgeProd(16)=0.01
      AgeProd(17)=0.01
      AgeProd(18)=0.01
      AgeProd(19)=0.01
      AgeProd(20)=0.01

      tempI1=0
      do j=1,nHF*nHF
       Regcoefs0(tempI1+1,j)=WageGrid(2)
       Regcoefs0(tempI1+2,j)=Rent1grid(2)
       Regcoefs0(tempI1+3,j)=Rent2grid(2)
       Regcoefs0(tempI1+4,j)=RP1grid(1)
       Regcoefs0(tempI1+5,j)=RP2grid(1)
       Regcoefs0(tempI1+6,j)=H1grid(2)
       Regcoefs0(tempI1+7,j)=H2grid(2)
       Regcoefs0(tempI1+8,j)=0
       Regcoefs0(tempI1+9,j)=0
       Regcoefs0(tempI1+10,j)=0
       Regcoefs0(tempI1+11,j)=1.0
       Regcoefs0(tempI1+12,j)=1.0
       Regcoefs0(tempI1+13,j)=WageGrid(2)*0.3*real(nAgent)
      end do
      do i=1,nRegr
      do j=1,nHF*nHF
       Regcoefs1(i,j)=0
       Regcoefs2(i,j)=0
       Regcoefs3(i,j)=0
       Regcoefs4(i,j)=0
       Regcoefs5(i,j)=0
       Regcoefs6(i,j)=0
       Regcoefs7(i,j)=0
       Regcoefs8(i,j)=0
       Regcoefs9(i,j)=0
       Regcoefs10(i,j)=0
       Regcoefs11(i,j)=0
       if(i.eq.1) then
        RegcoefsMin(i,j)=WageGrid(1)
        RegcoefsMax(i,j)=WageGrid(nWage)
       end if
       if(i.eq.2) then
        RegcoefsMin(i,j)=Rent1grid(1)
        RegcoefsMax(i,j)=Rent1grid(nRent1)
       end if
       if(i.eq.3) then
        RegcoefsMin(i,j)=Rent2grid(1)
        RegcoefsMax(i,j)=Rent2grid(nRent2)
       end if
       if(i.eq.4) then
        RegcoefsMin(i,j)=RP1grid(1)
        RegcoefsMax(i,j)=RP1grid(nRP1)
       end if
       if(i.eq.5) then
        RegcoefsMin(i,j)=RP2grid(1)
        RegcoefsMax(i,j)=RP2grid(nRP2)
       end if
       if(i.eq.6) then
        RegcoefsMin(i,j)=H1grid(1)
        RegcoefsMax(i,j)=H1grid(nH1)
       end if
       if(i.eq.7) then
        RegcoefsMin(i,j)=H2grid(1)
        RegcoefsMax(i,j)=H2grid(nH2)
       end if
       if(i.eq.8) then
        RegcoefsMin(i,j)=0.0
        RegcoefsMax(i,j)=0.1
       end if
       if(i.eq.9) then
        RegcoefsMin(i,j)=0.0
        RegcoefsMax(i,j)=1.0
       end if
       if(i.eq.10) then
        RegcoefsMin(i,j)=0.0
        RegcoefsMax(i,j)=1.0
       end if
       if(i.eq.11) then
        RegcoefsMin(i,j)=0.0
        RegcoefsMax(i,j)=2.0
       end if
       if(i.eq.12) then
        RegcoefsMin(i,j)=0.0
        RegcoefsMax(i,j)=2.0
       end if
       if(i.eq.13) then
        RegcoefsMin(i,j)=0.0
        RegcoefsMax(i,j)=2.0*real(nAgent)
       end if
      end do
      end do
      do i=1,nBeqDist*2
      do j=1,nHF*nHF
       RegcoefsBeq0(i,j)=0
       RegcoefsBeq1(i,j)=0
       RegcoefsBeqMin(i,j)=0
       RegcoefsBeqMax(i,j)=0
      end do
      end do

      call writedata(WageGrid,'WGgrid.txt',nWage,1,nWage,1)
      call writedata(Rent1Grid,'R1grid.txt',nRent1,1,nRent1,1)
      call writedata(Rent2Grid,'R2grid.txt',nRent2,1,nRent2,1)
      call writedata(RP1Grid,'P1grid.txt',nRP1,1,nRP1,1)
      call writedata(RP2Grid,'P2grid.txt',nRP2,1,nRP2,1)
      call writedata(H1Grid,'H1grid.txt',nH1,1,nH1,1)
      call writedata(H2Grid,'H2grid.txt',nH2,1,nH2,1)
      call writedataNW(NWgridAll,'NWgrid.txt',nAge*nDZ,nNW,nAge*nDZ,nNW)
      call writedata(HFgrid0,'HFgri0.txt',nHF,nLOC,nHF,nLOC)
      call writedata(HFgrid1,'HFgri1.txt',nHF,nLOC,nHF,nLOC)
      call writedata(HFVgrid,'FVgrid.txt',nHF,nLOC,nHF,nLOC)
      !call writedata(DZgrid,'DZgrid.txt',nDZ,1,nDZ,1)
      call writedata(SSIdist,'SSdist.txt',nDZ,1,nDZ,1)
      call writedata(TrProbDZ,'ProbDZ.txt',nDZ,nDZ,nDZ,nDZ)
      call writedata(TrProbHF,'ProbHF.txt',nHF,nHF,nHF,nHF)
      call writedata(AgeProd,'AgePrd.txt',nAge,1,nAge,1)

!      call writedata(Regcoefs0,'Coef00.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs1,'Coef01.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs2,'Coef02.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs3,'Coef03.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs4,'Coef04.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs5,'Coef05.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs6,'Coef06.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs7,'Coef07.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs8,'Coef08.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs9,'Coef09.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
!      call writedata(Regcoefs10,'Coef10.txt',nRegr,nHF*nHF,
!     1 nRegr,nHF*nHF)
!      call writedata(Regcoefs11,'Coef11.txt',nRegr,nHF*nHF,
!     1 nRegr,nHF*nHF)
!      call writedata(RegcoefsMin,'CoefMn.txt',nRegr,nHF*nHF,
!     1 nRegr,nHF*nHF)
!      call writedata(RegcoefsMax,'CoefMx.txt',nRegr,nHF*nHF,
!     1 nRegr,nHF*nHF)
!      call writedata(RegcoefsBeq0,'CoefB0.txt',2*nBeqDist,nHF*nHF,
!     1                                           2*nBeqDist,nHF*nHF)
!      call writedata(RegcoefsBeq1,'CoefB1.txt',2*nBeqDist,nHF*nHF,
!     1                                           2*nBeqDist,nHF*nHF)
!      call writedata(RegcoefsBeqMin,'CoefBn.txt',
!     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)
!      call writedata(RegcoefsBeqMax,'CoefBx.txt',
!     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)


!      call makenwgrid(nAge,nDZ,nNW,NWmin,NWmax)

      call itime(mytime)
      write(6,*) 0,mytime

      do i=1,10

      if(mod(i,10).eq.0) then
       flagWelf=1
      else
       flagWelf=0
      end if

      call DP(nAgg,nInd,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,
     1     nLOC,nRC,nDZ,nRClast,nAge,nRet,nDepr,nBeqDist,
     1     PriceBond,thetaRes,thetaInv,deprH,
     1     deprINV0,beta0,gamma0,alphaC,alphaH,alphaN,ElastCH,ElastCN,
     1     lambda0,tau0,lambdaBase,tauBase,
     1     chi0,HoursMin,CluxCut,CluxCost,Z1shiftAll,
     1     Z1shiftSize,Z1shiftCut,CommCost,CommCostFin,LeisureMin,
     1     taxss,taxprop,taxpropOOT,PubGood,DeathExp,
     1     HresMin,RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,
     1     ProfitRedist,RCinccut,RChsize,RCrentred,RCshare,RCprobStay,
     1     nAgent,nFirmC,nFirm1,nFirm2,NumRetired,NWmin,NWmax,nRegr,
     1     UncondDistDZ,BeqStrength,BeqLux,BetaRel,DeprGrid,DeprProb,
     1     fracBeq,RCsubs,flagRCstay)

      call simulate(nAgg,nInd,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,
     1     nHF,nLOC,nRC,nDZ,nRClast,nAge,nRet,nDepr,nBeqDist,
     1     PriceBond,thetaRes,thetaInv,deprH,
     1     deprINV0,beta0,gamma0,alphaC,alphaH,alphaN,ElastCH,ElastCN,
     1     lambda0,tau0,lambdaBase,tauBase,
     1     chi0,HoursMin,CluxCut,CluxCost,CommCost,
     1     CommCostFin,LeisureMin,taxss,taxprop,taxpropOOT,DeathExp,
     1     HresMin,RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,
     1     ProfitRedist,RCinccut,RChsize,RCrentred,RCshare,RCprobStay,
     1     flagWelf,nAgent,nFirmC,nFirm1,nFirm2,nAgent0,NWmin,NWmax,
     1     TotYears,NumDeadR,NumDeadW,nRegr,output,outputWelf,outputErr,
     1     TrProbDZuncond,UncondDistDZ,DeprGrid,DeprProb,fracBeq,RCsubs,
     1     flagRCstay,kappa2,kappa3,BetaRel,Z1shiftCut,Z1shiftAll,
     1     Z1shiftSize)

      tempR1=NumBorn*real(nAgent0)/real(nAgent)
      call computemoments1(TotYears,nAgent0,nAgent,
     1 nLOC,nDZ,nAge,nRet,nHF,DZgrid,SSIdist,AgeProd,
     1 RCinccut,RChsize,RCrentred,RCshare,PriceBond,deprH,
     1 taxss,taxprop,taxpropOOT,RTSH0loc1,RTSH0loc2,HBARloc1,HBARloc2,
     1 tempR1,HFgrid0,HFgrid1,output,outputWelf,outputErr,
     1 popShare1,fracRet,rentDiff,incDiff,MedIncomeWorker,RCshareRent,
     1 RCshareAll,fracSameRC,RCsubs,ProfitRedist,lambda0,tau0,
     1 lambdaBase,tauBase)

!      call makenwgrid(nAge,nDZ,nNW,NWmin,NWmax)

!the code below updates various quantities to match certain moments rather than doing this by hand
! -use pop1/(pop1+pop2) to update RTSH
! -use Hres to update H1grid and H2grid
! -use Rent1/Rent2 to update commcost (should be 1.63)
! -use Rent1 to update Rent1grid, Rent2 to update Rent2grid
! -use average house size to update RChsize (should be equal to average in each zone)
! -use average income to update RCinccut (should be 50% of average income)
! -use RC1/Renters1 and RC2/Renters2 to update RCshare (should be 53% and 24%)
      tempI1=0
      if(tempI1.eq.1) then

!no longer using CommCost to match rent difference, using Z1shiftAll instead
!      tempR1=CommCost(2,1)
!      CommCost(2,1)=CommCost(2,1)+0.01*(2.78-rentDiff)    !NYC: 2.78 ratio of Z1 to Z2 rent per square foot
!      CommCost(2,2)=CommCost(2,1)/3.0
!      write(6,'(a,f9.5,a,f9.5,a,f9.5)')
!     1 'OLD CommCost=',tempR1,' NEW CommCost=',CommCost(2,1),
!     1 ' rentDiff=',rentDiff

!no longer using CommCost to match rent difference, using Z1shiftAll instead
      tempR1=Z1shiftAll
      Z1shiftAll=Z1shiftAll+0.005*(1.03-rentDiff)    !NYC: 2.78 ratio of Z1 to Z2 rent per square foot
      write(6,'(a,f9.5,a,f9.5,a,f9.5)')
     1 'OLD Z1shiftAll=',tempR1,' NEW Z1shiftAll=',Z1shiftAll,
     1 ' rentDiff=',rentDiff

      tempR1=Z1shiftSize(1)
      Z1shiftSize(1)=Z1shiftSize(1)+0.002*(1.12-incDiff)   !NYC: 1.45, VAN: 0.95
      if(Z1shiftSize(1).lt.1.00) Z1shiftSize(1)=1.00
      write(6,'(a,f9.5,a,f9.5,a,f9.5)')
     1 'OLD Z1shiftSize(1)=',tempR1,' NEW Z1shiftSize(1)=',
     1 Z1shiftSize(1),' incDiff=',incDiff

      tempR1=Z1shiftSize(2)
      Z1shiftSize(2)=Z1shiftSize(2)+0.005*(0.84*fracRet(2)-fracRet(1))    !NYC: 0.91, VAN: 0.93
      if(Z1shiftSize(2).lt.1.00) Z1shiftSize(2)=1.00
      write(6,'(a,f9.5,a,f9.5,a,f9.5,f9.5)')
     1 'OLD Z1shiftSize(2)=',tempR1,' NEW Z1shiftSize(2)=',
     1 Z1shiftSize(2),' fracRet=',fracRet(1),fracRet(2)

      tempR1=HBARloc1(1)
      HBARloc1(1)=HBARloc1(1)*(1.0+2.0*(0.228-popShare1))    !NYC: 10.5% of total lives in Manhattan
      HBARloc1(2)=HBARloc1(2)*(1.0+2.0*(0.228-popShare1))
      if(HBARloc1(1).lt.0.01) HBARloc1(1)=0.01
      if(HBARloc1(2).lt.0.01) HBARloc1(2)=0.01
      !HBARloc1(1)=HBARloc2(1)*0.0238                          !NYC: 0.0238, VAN: 0.061
      !HBARloc1(2)=HBARloc2(2)*0.0238
      write(6,'(a,f9.5,a,f9.5,a,f8.4)')
     1 'OLD HBARloc1=',tempR1,' NEW HBARloc1=',HBARloc1(1),
     1 ' popShare1=',popShare1

!      do iHF=1,nHF

!      tempR1=RCinccut(1,iHF)
!      RCinccut(1,iHF)=0.75*RCinccut(1,iHF)+0.25*(0.38*MedIncomeWorker)
!      RCinccut(2,iHF)=RCinccut(1,iHF)
!      if(iHF.eq.1) then
!      write(6,'(a,f8.4,a,f8.4,a,f8.4)')
!     1 'OLD RCinccut=',tempR1,' NEW RCinccut=',RCinccut(1,iHF),
!     1 ' MedIncome=',MedIncomeWorker                !NYC: 2.0, VAN: 0.53
!      end if

!      RChsize(1,iHF)=0.75*RChsize(1,iHF)+0.25*(0.64*MedIncomeWorker)                     !NYC: 0.2, VAN: 0.2
!      RChsize(2,iHF)=0.75*RChsize(2,iHF)+0.25*(0.64*MedIncomeWorker)                     !NYC: 0.2, VAN: 0.2

!      tempR1=RCshare(1,iHF)
!      !RCshare(1,iHF)=RCshare(1,iHF)+0.25*(0.169-RCshareRent(1,iHF))                   !NYC: 0.169, VAN: 0.173
!      RCshare(1,iHF)=RCshare(1,iHF)+0.25*(0.1299-RCshareAll(1,iHF))
!      if(RCshare(1,iHF).lt.0.00) RCshare(1,iHF)=0.00
!      if(RCshare(1,iHF).gt.0.99) RCshare(1,iHF)=0.99
!      if(iHF.eq.1) then
!      write(6,'(a,f8.4,a,f8.4,a,f8.4)')
!     1 'OLD RCshare1=',tempR1,' NEW RCshare1=',RCshare(1,iHF),
!     1 ' RCshareAll1=',RCshareAll(1,iHF)
!      end if

!      tempR1=RCshare(2,iHF)
!      !RCshare(2,iHF)=RCshare(2,iHF)+0.25*(0.104-RCshareRent(2,iHF))                   !NYC: 0.104, VAN: 0.158
!      RCshare(2,iHF)=RCshare(2,iHF)+0.25*(0.0469-RCshareAll(2,iHF))
!      if(RCshare(2,iHF).lt.0.00) RCshare(2,iHF)=0.00
!      if(RCshare(2,iHF).gt.0.99) RCshare(2,iHF)=0.99
!      if(iHF.eq.1) then
!      write(6,'(a,f8.4,a,f8.4,a,f8.4)')
!     1 'OLD RCshare2=',tempR1,' NEW RCshare2=',RCshare(2,iHF),
!     1 ' RCshareAll2=',RCshareAll(2,iHF)
!      end if

!      end do
      
!      tempR1=RCprobStay(1)
!      RCprobStay(1)=RCprobStay(1)+0.25*(0.231-fracSameRC) !NYC: 0.231
!      if (RCprobStay(1).lt.0.00) RCprobStay(1)=0.00
!      if (RCprobStay(1).gt.1.00) RCprobStay(1)=1.00
!      RCprobStay(2)=RCprobStay(1)
!      write(6,'(a,f8.4,a,f8.4,a,f8.4)')
!     1 'OLD RCprobStay=',tempR1,' NEW RCprobStay=',RCprobStay(1),
!     1 ' fracSameRC=',fracSameRC

!      write(6,'(a,f8.4,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'OLD Rent1grid=',(Rent1grid(j),j=1,nRent1),' Rent1=',Rent(1)
!      Rent1grid(1)=Rent(1)-.5*0.02-0.02
!      Rent1grid(2)=Rent(1)-.5*0.02
!      Rent1grid(3)=Rent(1)+.5*0.02
!      Rent1grid(4)=Rent(1)+.5*0.02+0.02
!      write(6,'(a,f8.4,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'NEW Rent1grid=',(Rent1grid(j),j=1,nRent1)
!      call writedata(Rent1Grid,'R1grid.txt',nRent1,1,nRent1,1)

!      write(6,'(a,f8.4,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'OLD Rent2grid=',(Rent2grid(j),j=1,nRent2),' Rent2=',Rent(2)
!      Rent2grid(1)=Rent(2)-.5*0.02-0.02
!      Rent2grid(2)=Rent(2)-.5*0.02
!      Rent2grid(3)=Rent(2)+.5*0.02
!      Rent2grid(4)=Rent(2)+.5*0.02+0.02
!      write(6,'(a,f8.4,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'NEW Rent2grid=',(Rent2grid(j),j=1,nRent1)
!      call writedata(Rent2Grid,'R2grid.txt',nRent2,1,nRent2,1)

!      write(6,'(a,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'OLD H1grid=',(H1grid(j),j=1,nH1),' H1=',Hres(1)
!      H1grid(1)=Hres(1)*0.6
!      H1grid(2)=Hres(1)
!      H1grid(3)=Hres(1)*1.4
!      if(H1grid(3).gt.HBARloc1(1)) H1grid(3)=Hres(1)*0.5+HBARloc1(1)*0.5
!      if(H1grid(3).lt.Hres(1)) H1grid(3)=Hres(1)+0.1
!      write(6,'(a,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'NEW H1grid=',(H1grid(j),j=1,nH1)
!      call writedata(H1grid,'H1grid.txt',nH1,1,nH1,1)

!      write(6,'(a,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'OLD H2grid=',(H2grid(j),j=1,nH1),' H2=',Hres(2)
!      H2grid(1)=Hres(2)*0.6
!      H2grid(2)=Hres(2)
!      H2grid(3)=Hres(2)*1.4
!      if(H2grid(3).gt.HBARloc2(1)) H2grid(3)=Hres(2)*0.5+HBARloc2(1)*0.5
!      if(H2grid(3).lt.Hres(2)) H2grid(3)=Hres(2)+0.1
!      write(6,'(a,f8.4,f8.4,f8.4,a,f8.4)')
!     1 'NEW H2grid=',(H2grid(j),j=1,nH2)
!      call writedata(H2grid,'H2grid.txt',nH2,1,nH2,1)

      end if


      call itime(mytime)
      write(6,*) i,mytime

      end do

      end

!------------------------------------------------------------------------
      SUBROUTINE DP(nAgg,nInd,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,
     1     nHF,nLOC,nRC,nDZ,nRClast,nAge,nRet,nDepr,nBeqDist,
     1     PriceBond,thetaRes,thetaInv,deprH,
     1     deprINV0,beta0,gamma0,alphaC,alphaH,alphaN,ElastCH,ElastCN,
     1     lambda0,tau0,lambdaBase,tauBase,
     1     chi0,HoursMin,CluxCut,CluxCost,
     1     Z1shiftAll,Z1shiftSize,Z1shiftCut,
     1     CommCost,CommCostFin,LeisureMin,taxss,taxprop,taxpropOOT,
     1     PubGood,DeathExp,
     1     HresMin,RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,
     1     ProfitRedist,RCinccut,RChsize,RCrentred,RCshare,RCprobStay,
     1     nAgent,nFirmC,nFirm1,nFirm2,NumRetired,NWmin,NWmax,nRegr,
     1     UncondDistDZ,BeqStrength,BeqLux,BetaRel,DeprGrid,DeprProb,
     1     fracBeq,RCsubs,flagRCstay)
      implicit none
      character(len=9) filename
      integer nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nLOC,nAgg
      integer iAgg,iHF,iH2,iH1,iRent2,iRent1,iRP2,iRP1,iWage,iHFnext,iDZ
      integer iLOC,iCchoice,iHchoice,nDZ,iState,iNW,nCchoice2,nHchoice2
      integer nCchoice0,nHchoice0,nCchoice1,nHchoice1,nRegr,nInd,iInd
      integer nCchoice3,nHchoice3,iAge,nAge,nRet,nAgent,nRC,nBeqDist
      integer iBeqDist,nRClast,iRClast,flagRCstay(nHF)
      parameter(nCchoice0=25,nHchoice0=25,nCchoice1=11,nHchoice1=11)
      parameter(nCchoice2=11,nHchoice2=11,nCchoice3=33,nHchoice3=11)
      real thetaRes,thetaInv,PriceBond,beta0,gamma0,alphaC,alphaH,alphaN
      real ElastCH,ElastCN,chi0,HoursMin,lambda0(nHF),tau0(nHF)
      real lambdaBase,tauBase,RCprobStay(nLOC)
      real deprH(nLOC),deprINV0
      real taxss,LaborIncome,HoursDemandLOC2,HoursDemand
      real ProfitC,ProfitLOC1,ProfitLOC2,LaborIncomePreTax
      real ProfitGrid(nAgg),ProfitRedist(3)
      real RTSC,RTSH0loc1,HBARloc1(nHF),RTSH0loc2,HBARloc2(nHF)
      real taxprop(nHF,nLOC),HresMin
      real RCinccut(nLOC,nHF),RChsize(nLOC,nHF),RCrentred(nLOC,nHF)
      real RCshare(nLOC,nHF)
      real RCavgrent(nLOC,nHF),RCprob(nAgg,nLOC),PHavg(nLOC)
      real BetaRel(nDZ)
      real ShareOwned(nAgg,nLOC),BeqStrength(nDZ),BeqLux(nDZ)
      real nFirmC,nFirm1,nFirm2,NWmin,NWmax,UncondDistDZ(1,nDZ)
      real DeathExp,taxpropOOT(nLOC),PubGood,UtilPubGood
      real HoursDemandC,HoursDemandLOC1,fracBeq
      real CchoiceGrid0(nCchoice0),HchoiceGrid0(nHchoice0)
      real EVnext,Cchoice,Hchoice,Bnext,NW,Rent1,Rent2,RP1,RP2,Wage
      real CchoiceMax,CchoiceMin,HchoiceMax,HchoiceMin,BeqProb(nAge)
      real CchoiceMax0,CchoiceMin0,HchoiceMax0,HchoiceMin0
      real CchoiceMax1,CchoiceMin1,HchoiceMax1,HchoiceMin1
      real CchoiceMax2,CchoiceMin2,HchoiceMax2,HchoiceMin2
      integer nCchoiceTemp0(nCchoice0+1+nCchoice1+nCchoice2+nCchoice3)
      integer nCchoiceTemp1(nCchoice0+1+nCchoice1+nCchoice2+nCchoice3)
      integer nHchoiceTemp0(nCchoice0+1+nCchoice1+nCchoice2+nCchoice3)
      integer nHchoiceTemp1(nCchoice0+1+nCchoice1+nCchoice2+nCchoice3)
      integer tempI1,tempI2,tempI3,tempI4
      integer iWageNext,iH1next,iH2next,iRP1next,iRP2next,nDepr,iDepr
      integer iRent1next,iRent2next,iRenter,nHchoiceTemp,flagRet
      real tempR1,tempR2,tempR3,tempR4
      real WageGrid(nWage),Rent1Grid(nRent1),Rent2Grid(nRent2)
      real NWgrid(nNW),NWgridAll(nAge*nDZ,nNW),NWgridNext(nNW)
      real RP1grid(nRP1),RP2grid(nRP2),Z1shiftAll
      real CluxCut(2),CluxCost(2),Z1shiftSize(2),Z1shiftCut(2)
      real H1grid(nH1),H2grid(nH2),HFVgrid(nHF,nLOC)
      real HFgrid0(nHF,nLOC),HFgrid1(nHF,nLOC)
      real PensionGrid(nAgg),BeqGrid(nAgg,nHF),AgeProd(nAge),CluxCost0
      real PropTaxIncome(nAgg),HchoiceUppBound
      integer flagUppBound
      real H1nextGrid(nAgg,nHF),H2nextGrid(nAgg,nHF)
      real Rent1nextGrid(nAgg,nHF),Rent2nextGrid(nAgg,nHF)
      real RP1nextGrid(nAgg,nHF),RP2nextGrid(nAgg,nHF),SSIdist(nDZ)
      real WageNextGrid(nAgg,nHF),CommCost(nLOC,2),DZgrid(nAge,nDZ)
      real CommCostFin(nLOC,2)
      real Rent(nLOC),RentNext(nLOC),PH(nLOC),PHnext(nLOC)
      real H1nextMult(nAgg,nHF),H2nextMult(nAgg,nHF),LeisureMin
      real Rent1nextMult(nAgg,nHF),Rent2nextMult(nAgg,nHF)
      real RP1nextMult(nAgg,nHF),RP2nextMult(nAgg,nHF)
      real WageNextMult(nAgg,nHF),NWnext,Hours,Hres,Util
      real multH1,multH2,multRP1,multRP2,multWage,multRent1,multRent2
      integer H1nextSpot(nAgg,nHF),H2nextSpot(nAgg,nHF),iHFindex
      integer Rent1nextSpot(nAgg,nHF),Rent2nextSpot(nAgg,nHF)
      integer RP1nextSpot(nAgg,nHF),RP2nextSpot(nAgg,nHF),iRClastNext
      integer WageNextSpot(nAgg,nHF),i,iChoiceDisc,iRegression,iIndNext
      integer jH1,jH2,jRent1,jRent2,jRP1,jRP2,jWage,iAggNext,extrap(2)
      integer iNWnext,iStateNextL,iStateNextH,iStateNext,iDZnext
      real ValFun(nAgg*nInd,1),ValFun0(nAgg*nInd,1),dValFun(nAgg*nInd,1)
      real ValFunNW(nNW),dValFunNW(nNW),Vmax,VmaxCond,V
      real DeprGrid(nDepr),DeprProb(nDepr),TrProbDepr
!the policy function contains the following:
!2*(2+nRC)*nLOC --> first 2 is the consumption policy and the housing investment policy, second (2+nRC) is for renters, owners, and rent controlled renters (if nRC=1), third nLOC is at each location
!Thus the second dimension of policy is (iChoiceDisc-1)*2+1 (consumption) or (iChoiceDisc-1)*2+2 (housing investment)
!iChoiceDisc=(iRenter-1)*nLOC+iLOC where iLOC=(1,2)
!if nRC=0 then iRenter=(1=renter,2=owner). if nRC=1 then i=(1=renter,2=owner,3=rent controlled renter)
!Note that in simulation stage there is no need to interpolate between the discrete variables iRenter and iLOC
!instead, just choose optimal (C,Hres) conditional on every (iRenter,iLOC) and then choose which (iRenter,iLOC) gives best utility
!Similarly, the value function contains best value conditional on each possible (iRenter,iLOC)
!Also, iRenter=3 is not a choice for everyone. Agents are randomly allowed to have that choice
      real Policy(nAgg*nInd,2*(2+nRC)*nLOC)
      real ValFunCond(nAgg*nInd,(2+nRC)*nLOC+1)
      real Vnext7(2,2,2,2,2,2,2),Vnext6(2,2,2,2,2,2),Vnext5(2,2,2,2,2)
      real Vnext4(2,2,2,2),Vnext3(2,2,2),Vnext2(2,2),Vnext1(2),Vnext
      real Vnext1beq(2,nBeqDist),Vnext2beq(2,2,nBeqDist)
      real Vnext3beq(2,2,2,nBeqDist),Vnext4beq(2,2,2,2,nBeqDist)
      real Vnext5beq(2,2,2,2,2,nBeqDist),Vnext6beq(2,2,2,2,2,2,nBeqDist)
      real Vnext7beq(2,2,2,2,2,2,2,nBeqDist)
      real TrProbHF(nHF,nHF),TrProbDZ(nDZ,nDZ),TrProb,ProbDeath(nAge)
      !real EValFunNextrid(nAgg,nLOC*nBnext0*nHnext0)
      real ValFunNext(nAgg*nInd,nHF),dValFunNext(nAgg*nInd,nHF)
      real PH1grid(nAgg,1),PH2grid(nAgg,1),PH1,PH2,PH1next,PH2next
      real PH1grid0(nAgg,1),PH2grid0(nAgg,1),EPH1next,EPH2next,Normalize
      real PH1nextGrid(nAgg,nHF),PH2nextGrid(nAgg,nHF),NumRetired
      double precision MinVal
      real Regcoefs1(nRegr,nHF*nHF),Regcoefs2(nRegr,nHF*nHF)
      real Regcoefs3(nRegr,nHF*nHF),Regcoefs4(nRegr,nHF*nHF)
      real Regcoefs5(nRegr,nHF*nHF),Regcoefs6(nRegr,nHF*nHF)
      real Regcoefs7(nRegr,nHF*nHF),Regcoefs0(nRegr,nHF*nHF)
      real Regcoefs8(nRegr,nHF*nHF),Regcoefs9(nRegr,nHF*nHF)
      real Regcoefs10(nRegr,nHF*nHF),Regcoefs11(nRegr,nHF*nHF)
      real RegcoefsMin(nRegr,nHF*nHF),RegcoefsMax(nRegr,nHF*nHF)
      real RegcoefsBeq0(2*nBeqDist,nHF*nHF)
      real RegcoefsBeq1(2*nBeqDist,nHF*nHF)
      real RegcoefsBeqMin(2*nBeqDist,nHF*nHF)
      real RegcoefsBeqMax(2*nBeqDist,nHF*nHF)
      real VA(nAge),QA(nAge),Q,Ubar,Cint
      real param0,param1,param2,HoursConst0,HoursConst1,UtilConst0
      real HouseConst0,HouseConst1,HouseConst2,UtilConst1,UtilConst2
      real RegRHS(12),PHnextMin(nLOC),Pension
      real NWnextBeqRec(nBeqDist),VnextBeqRec(nBeqDist)
      real EvnextBeq,multNWnextBeqRec(nBeqDist),RCprobTemp(nLOC)
      integer iIndNextBeqRec(nBeqDist),flagMinVal,iHoursChoice
      real BeqDist(nAgg,nHF,nBeqDist*2),ForDemTot(2),CommCostTemp
      real r0,HoursConst2,HoursConst3,HoursGrid0(3,2),HoursGrid(3,2)
      real TaxableIncome,HSVtax,HSVtaxBase,HresMinVoucher
      real RCsubs(nLOC,nHF),RCavgrentDev(nLOC,nHF)

      MinVal=-(10.0**30.0)
      param0=(1.0-gamma0)*(1.0-alphaN)
      param1=((chi0*alphaN/(alphaC*(1.0-alphaN)))**
     1       (1.0/(1.0-chi0*ElastCN)))
      param2=(1.0-ElastCN)/(1.0-chi0*ElastCN)
      r0=1.0-PriceBond

      do iHF=1,nHF
      do i=1,nLOC
       RCavgrent(i,iHF)=
     1   1.0-RCshare(i,iHF)+RCshare(i,iHF)*(1.0-RCrentred(i,iHF)) !True rent received and price paid relative to market, once accounting for being forced to buy RCshare rent controlled units
       RCavgrentDev(i,iHF)=1.0-RCshare(i,iHF)+
     1  RCshare(i,iHF)*(1.0-RCrentred(i,iHF))*(1.0+RCsubs(i,iHF))
      end do
      end do

      call readdata(ProbDeath,'prbdth.txt',nAge,1,nAge,1)
      call readdata(BeqProb,'BeqPrb.txt',nAge,1,nAge,1)
      do i=1,nAge
       if(ProbDeath(i).gt.1.0) ProbDeath(i)=1.0
       if(BeqProb(i).gt.1.0) BeqProb(i)=1.0
      end do
      call readdata(WageGrid,'WGgrid.txt',nWage,1,nWage,1)
      call readdata(Rent1Grid,'R1grid.txt',nRent1,1,nRent1,1)
      call readdata(Rent2Grid,'R2grid.txt',nRent2,1,nRent2,1)
      call readdata(RP1Grid,'P1grid.txt',nRP1,1,nRP1,1)
      call readdata(RP2Grid,'P2grid.txt',nRP2,1,nRP2,1)
      call readdata(H1Grid,'H1grid.txt',nH1,1,nH1,1)
      call readdata(H2Grid,'H2grid.txt',nH2,1,nH2,1)
      call readdata(NWgridAll,'NWgrid.txt',nAge*nDZ,nNW,nAge*nDZ,nNW)
      call readdata(HFgrid0,'HFgri0.txt',nHF,nLOC,nHF,nLOC)
      call readdata(HFgrid1,'HFgri1.txt',nHF,nLOC,nHF,nLOC)
      call readdata(HFVgrid,'FVgrid.txt',nHF,nLOC,nHF,nLOC)
      call readdata(DZgrid,'DZgrid.txt',nAge,nDZ,nAge,nDZ)
      call readdata(SSIdist,'SSdist.txt',nDZ,1,nDZ,1)
      call readdata(TrProbDZ,'ProbDZ.txt',nDZ,nDZ,nDZ,nDZ)
      call readdata(TrProbHF,'ProbHF.txt',nHF,nHF,nHF,nHF)
      call readdata(AgeProd,'AgePrd.txt',nAge,1,nAge,1)
      call readdata(Regcoefs0,'Coef00.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs1,'Coef01.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs2,'Coef02.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs3,'Coef03.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs4,'Coef04.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs5,'Coef05.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs6,'Coef06.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs7,'Coef07.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs8,'Coef08.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs9,'Coef09.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs10,'Coef10.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs11,'Coef11.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsMin,'CoefMn.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsMax,'CoefMx.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsBeq0,'CoefB0.txt',2*nBeqDist,nHF*nHF,
     1                                           2*nBeqDist,nHF*nHF)
      call readdata(RegcoefsBeq1,'CoefB1.txt',2*nBeqDist,nHF*nHF,
     1                                           2*nBeqDist,nHF*nHF)
      call readdata(RegcoefsBeqMin,'CoefBn.txt',
     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)
      call readdata(RegcoefsBeqMax,'CoefBx.txt',
     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)

!analytic solution
      Q=PriceBond
      Ubar=((Rent1grid(2)**(-alphaH*(1.0-alphaN)))*
     1      (WageGrid(2)**(-alphaN))*
     1      (alphaC**(alphaC*(1.0-alphaN)))*
     1      (alphaH**(alphaH*(1.0-alphaN)))*(alphaN**alphaN))**
     1      (1.0-gamma0)
      tempR1=beta0*(Q**(gamma0-1.0))
      VA(1)=Ubar
      QA(1)=0.0
      do i=2,nAge
       if(abs(VA(i-1)).lt.0.0001) then
        VA(i)=alphaC*Ubar
       else
        VA(i)=tempR1*VA(i-1)*
     1       (1.0+(tempR1*VA(i-1)/Ubar)**(-1.0/gamma0))**gamma0
       end if
       QA(i)=Q/(1.0+Q-QA(i-1))
      end do


!Form coarse grids for initial optimization over C and H
      tempR1=1.0-thetaRes
      if(tempR1.lt.0.1) tempR1=0.1
      do iHchoice=1,nHchoice0
       HchoiceGrid0(iHchoice)=0.0+(1.0/tempR1)*NWmax*
     1                    real(iHchoice-1)/real(nHchoice0-1)
      end do
      do iCchoice=1,nCchoice0+1
       if(iCchoice.le.nCchoice0) then
        CchoiceGrid0(iCchoice)=
     1   0.001+5.0*real(iCchoice-1)/real(nCchoice0-1)
       end if
       nCchoiceTemp0(iCchoice)=0
       nCchoiceTemp1(iCchoice)=nCchoice0
       nHchoiceTemp0(iCchoice)=0
       nHchoiceTemp1(iCchoice)=nHchoice0
      end do
!Create intermediate variables to do finer interpolation. These variables define the bounds for iCchoice and iHchoice at each finer step
      do iCchoice=nCchoice0+1+1,nCchoice0+1+nCchoice1
       nCchoiceTemp0(iCchoice)=nCchoice0+1
       nCchoiceTemp1(iCchoice)=nCchoice1
       nHchoiceTemp0(iCchoice)=nHchoice0
       nHchoiceTemp1(iCchoice)=nHchoice1
      end do
      do iCchoice=nCchoice0+1+nCchoice1+1,
     1            nCchoice0+1+nCchoice1+nCchoice2
       nCchoiceTemp0(iCchoice)=nCchoice0+1+nCchoice1
       nCchoiceTemp1(iCchoice)=nCchoice2
       nHchoiceTemp0(iCchoice)=nHchoice0+nHchoice1
       nHchoiceTemp1(iCchoice)=nHchoice2
      end do
      do iCchoice=nCchoice0+1+nCchoice1+nCchoice2+1,
     1            nCchoice0+1+nCchoice1+nCchoice2+nCchoice3
       nCchoiceTemp0(iCchoice)=nCchoice0+1+nCchoice1+nCchoice2
       nCchoiceTemp1(iCchoice)=nCchoice3
       nHchoiceTemp0(iCchoice)=nHchoice0+nHchoice1+nHchoice2
       nHchoiceTemp1(iCchoice)=nHchoice3
      end do

!This piece of code computes the belief about next period's state as a function of today's state and the realized shock
!It also computes the location of next period's state on the grid to speed up calculations later
      do iAgg=1,nAgg
!       iAgg=(iWage-1)*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
!     1      (iRent1-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
!     1      (iRent2-1)*nRP1*nRP2*nH1*nH2*nHF+
!     1      (iRP1-1)*nRP2*nH1*nH2*nHF+
!     1      (iRP2-1)*nH1*nH2*nHF+(iH1-1)*nH2*nHF+(iH2-1)*nHF+iHF
       iHF=mod(iAgg-1,nHF)+1
       tempI1=1+(iAgg-iHF)/nHF
       iH2=mod(tempI1-1,nH2)+1
       tempI1=1+(tempI1-iH2)/nH2
       iH1=mod(tempI1-1,nH1)+1
       tempI1=1+(tempI1-iH1)/nH1
       iRP2=mod(tempI1-1,nRP2)+1
       tempI1=1+(tempI1-iRP2)/nRP2
       iRP1=mod(tempI1-1,nRP1)+1
       tempI1=1+(tempI1-iRP1)/nRP1
       iRent2=mod(tempI1-1,nRent2)+1
       tempI1=1+(tempI1-iRent2)/nRent2
       iRent1=mod(tempI1-1,nRent1)+1
       iWage=1+(tempI1-iRent1)/nRent1
       RegRHS(1)=1
       RegRHS(2)=WageGrid(iWage)
       RegRHS(3)=Rent1grid(iRent1)
       RegRHS(4)=Rent2grid(iRent2)
       RegRHS(5)=RP1grid(iRP1)
       RegRHS(6)=RP2grid(iRP2)
       RegRHS(7)=H1grid(iH1)
       RegRHS(8)=H2grid(iH2)
       RegRHS(9)=0.5*(Rent1grid(iRent1)+Rent2grid(iRent2))
       RegRHS(10)=0.5*(RP1grid(iRP1)+RP2grid(iRP2))
       RegRHS(11)=0.5*(H1grid(iH1)+H2grid(iH2))
       RegRHS(12)=0.0

       do iHFnext=1,nHF

        !WageNextGrid(iAgg,iHFnext)=WageGrid(2)
        !Rent1nextGrid(iAgg,iHFnext)=Rent1grid(2)
        !Rent2nextGrid(iAgg,iHFnext)=Rent2grid(2)
        !RP1nextGrid(iAgg,iHFnext)=RP1grid(1)
        !RP2nextGrid(iAgg,iHFnext)=RP2grid(1)
        !H1nextGrid(iAgg,iHFnext)=H1grid(2)
        !H2nextGrid(iAgg,iHFnext)=H2grid(2)

        iHFindex=(iHF-1)*nHF+iHFnext

        do iRegression=1,nRegr
         tempR1=RegCoefs0(iRegression,iHFindex)*RegRHS(1)+
     1          RegCoefs1(iRegression,iHFindex)*RegRHS(2)+
     1          RegCoefs2(iRegression,iHFindex)*RegRHS(3)+
     1          RegCoefs3(iRegression,iHFindex)*RegRHS(4)+
     1          RegCoefs4(iRegression,iHFindex)*RegRHS(5)+
     1          RegCoefs5(iRegression,iHFindex)*RegRHS(6)+
     1          RegCoefs6(iRegression,iHFindex)*RegRHS(7)+
     1          RegCoefs7(iRegression,iHFindex)*RegRHS(8)+
     1          RegCoefs8(iRegression,iHFindex)*RegRHS(9)+
     1          RegCoefs9(iRegression,iHFindex)*RegRHS(10)+
     1          RegCoefs10(iRegression,iHFindex)*RegRHS(11)+
     1          RegCoefs11(iRegression,iHFindex)*RegRHS(12)

         if(iRegression.eq.1) WageNextGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.2) Rent1nextGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.3) Rent2nextGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.4) RP1nextGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.5) RP2nextGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.6) H1nextGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.7) H2nextGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.8) BeqGrid(iAgg,iHFnext)=tempR1
         if(iRegression.eq.13) PensionGrid(iAgg)=tempR1!*taxss/NumRetired
!Even though there are 4 separate regressions (iHF x iHFnext), this is actually a contemporaneous regression so only need to condition on iHF
!For this reason, throw out the (1,2) and (2,1) cases since they should be identical to (1,1) and (2,2) but have fewer datapoints
         if(iHF.eq.iHFnext) then
          if(iRegression.eq.9) RCprob(iAgg,1)=tempR1
          if(iRegression.eq.10) RCprob(iAgg,2)=tempR1
          if(RCprob(iAgg,1).lt.0.00) RCprob(iAgg,1)=0.0
          if(RCprob(iAgg,1).gt.0.99) RCprob(iAgg,1)=0.99
          if(RCprob(iAgg,2).lt.0.00) RCprob(iAgg,2)=0.0
          if(RCprob(iAgg,2).gt.0.99) RCprob(iAgg,2)=0.99
          if(iRegression.eq.11) ShareOwned(iAgg,1)=tempR1
          if(iRegression.eq.12) ShareOwned(iAgg,2)=tempR1
          if(ShareOwned(iAgg,1).lt.0.01) ShareOwned(iAgg,1)=0.01
          if(ShareOwned(iAgg,2).lt.0.01) ShareOwned(iAgg,2)=0.01
          if(ShareOwned(iAgg,1).gt.1.00) ShareOwned(iAgg,1)=1.00
          if(ShareOwned(iAgg,2).gt.1.00) ShareOwned(iAgg,2)=1.00
         end if
        end do

        do iRegression=1,nBeqDist*2
         tempR1=RegCoefsBeq0(iRegression,iHFindex)*RegRHS(1)+
     1          RegCoefsBeq1(iRegression,iHFindex)*RegRHS(2)
         if(tempR1.lt.RegCoefsBeqMin(iRegression,iHFindex)) then
          tempR1=RegCoefsBeqMin(iRegression,iHFindex)
         end if
         if(tempR1.gt.RegCoefsBeqMax(iRegression,iHFindex)) then
          tempR1=RegCoefsBeqMax(iRegression,iHFindex)
         end if
         BeqDist(iAgg,iHFnext,iRegression)=tempR1
        end do

!        if(WageNextGrid(iAgg,iHFnext).lt.RegcoefsMin(1,iHFindex))
!     1     WageNextGrid(iAgg,iHFnext)=RegcoefsMin(1,iHFindex)
!        if(WageNextGrid(iAgg,iHFnext).gt.RegcoefsMax(1,iHFindex))
!     1     WageNextGrid(iAgg,iHFnext)=RegcoefsMax(1,iHFindex)
!        if(Rent1NextGrid(iAgg,iHFnext).lt.RegcoefsMin(2,iHFindex))
!     1     Rent1NextGrid(iAgg,iHFnext)=RegcoefsMin(2,iHFindex)
!        if(Rent1NextGrid(iAgg,iHFnext).gt.RegcoefsMax(2,iHFindex))
!     1     Rent1NextGrid(iAgg,iHFnext)=RegcoefsMax(2,iHFindex)
!        if(Rent2NextGrid(iAgg,iHFnext).lt.RegcoefsMin(3,iHFindex))
!     1     Rent2NextGrid(iAgg,iHFnext)=RegcoefsMin(3,iHFindex)
!        if(Rent2NextGrid(iAgg,iHFnext).gt.RegcoefsMax(3,iHFindex))
!     1     Rent2NextGrid(iAgg,iHFnext)=RegcoefsMax(3,iHFindex)
!        if(RP1NextGrid(iAgg,iHFnext).lt.RegcoefsMin(4,iHFindex))
!     1     RP1NextGrid(iAgg,iHFnext)=RegcoefsMin(4,iHFindex)
!        if(RP1NextGrid(iAgg,iHFnext).gt.RegcoefsMax(4,iHFindex))
!     1     RP1NextGrid(iAgg,iHFnext)=RegcoefsMax(4,iHFindex)
!        if(RP2NextGrid(iAgg,iHFnext).lt.RegcoefsMin(5,iHFindex))
!     1     RP2NextGrid(iAgg,iHFnext)=RegcoefsMin(5,iHFindex)
!        if(RP2NextGrid(iAgg,iHFnext).gt.RegcoefsMax(5,iHFindex))
!     1     RP2NextGrid(iAgg,iHFnext)=RegcoefsMax(5,iHFindex)
!        if(H1NextGrid(iAgg,iHFnext).lt.RegcoefsMin(6,iHFindex))
!     1     H1NextGrid(iAgg,iHFnext)=RegcoefsMin(6,iHFindex)
!        if(H1NextGrid(iAgg,iHFnext).gt.RegcoefsMax(6,iHFindex))
!     1     H1NextGrid(iAgg,iHFnext)=RegcoefsMax(6,iHFindex)
!        if(H2NextGrid(iAgg,iHFnext).lt.RegcoefsMin(7,iHFindex))
!     1     H2NextGrid(iAgg,iHFnext)=RegcoefsMin(7,iHFindex)
!        if(H2NextGrid(iAgg,iHFnext).gt.RegcoefsMax(7,iHFindex))
!     1     H2NextGrid(iAgg,iHFnext)=RegcoefsMax(7,iHFindex)
        if(BeqGrid(iAgg,iHFnext).lt.RegcoefsMin(8,iHFindex))
     1     BeqGrid(iAgg,iHFnext)=RegcoefsMin(8,iHFindex)
        if(BeqGrid(iAgg,iHFnext).gt.RegcoefsMax(8,iHFindex))
     1     BeqGrid(iAgg,iHFnext)=RegcoefsMax(8,iHFindex)

        call findspot(H1grid,nH1,H1nextGrid(iAgg,iHFnext),iH1,tempI1)
        H1nextSpot(iAgg,iHFnext)=tempI1
        tempR1=(H1nextGrid(iAgg,iHFnext)-H1grid(tempI1))/
     1         (H1grid(tempI1+1)-H1grid(tempI1))
        if(tempR1.lt.0.0) tempR1=0.0
        if(tempR1.gt.1.0) tempR1=1.0
        H1nextMult(iAgg,iHFnext)=tempR1

        call findspot(H2grid,nH2,H2nextGrid(iAgg,iHFnext),iH2,tempI1)
        H2nextSpot(iAgg,iHFnext)=tempI1
        tempR1=(H2nextGrid(iAgg,iHFnext)-H2grid(tempI1))/
     1         (H2grid(tempI1+1)-H2grid(tempI1))
        if(tempR1.lt.0.0) tempR1=0.0
        if(tempR1.gt.1.0) tempR1=1.0
        H2nextMult(iAgg,iHFnext)=tempR1

        call findspot(Rent1grid,nRent1,Rent1nextGrid(iAgg,iHFnext),
     1                iRent1,tempI1)
        Rent1nextSpot(iAgg,iHFnext)=tempI1
        tempR1=(Rent1nextGrid(iAgg,iHFnext)-Rent1grid(tempI1))/
     1         (Rent1grid(tempI1+1)-Rent1grid(tempI1))
        if(tempR1.lt.0.0) tempR1=0.0
        if(tempR1.gt.1.0) tempR1=1.0
        Rent1nextMult(iAgg,iHFnext)=tempR1

        call findspot(Rent2grid,nRent2,Rent2nextGrid(iAgg,iHFnext),
     1                iRent2,tempI1)
        Rent2nextSpot(iAgg,iHFnext)=tempI1
        tempR1=(Rent2nextGrid(iAgg,iHFnext)-Rent2grid(tempI1))/
     1         (Rent2grid(tempI1+1)-Rent2grid(tempI1))
        if(tempR1.lt.0.0) tempR1=0.0
        if(tempR1.gt.1.0) tempR1=1.0
        Rent2nextMult(iAgg,iHFnext)=tempR1

        call findspot(RP1grid,nRP1,RP1nextGrid(iAgg,iHFnext),
     1                iRP1,tempI1)
        RP1nextSpot(iAgg,iHFnext)=tempI1
        tempR1=(RP1nextGrid(iAgg,iHFnext)-RP1grid(tempI1))/
     1         (RP1grid(tempI1+1)-RP1grid(tempI1))
        if(tempR1.lt.0.0) tempR1=0.0
        if(tempR1.gt.1.0) tempR1=1.0
        RP1nextMult(iAgg,iHFnext)=tempR1

        call findspot(RP2grid,nRP2,RP2nextGrid(iAgg,iHFnext),
     1                iRP2,tempI1)
        RP2nextSpot(iAgg,iHFnext)=tempI1
        tempR1=(RP2nextGrid(iAgg,iHFnext)-RP2grid(tempI1))/
     1         (RP2grid(tempI1+1)-RP2grid(tempI1))
        if(tempR1.lt.0.0) tempR1=0.0
        if(tempR1.gt.1.0) tempR1=1.0
        RP2nextMult(iAgg,iHFnext)=tempR1

        call findspot(WageGrid,nWage,WageNextGrid(iAgg,iHFnext),
     1                iWage,tempI1)
        WageNextSpot(iAgg,iHFnext)=tempI1
        tempR1=(WageNextGrid(iAgg,iHFnext)-WageGrid(tempI1))/
     1         (WageGrid(tempI1+1)-WageGrid(tempI1))
        if(tempR1.lt.0.0) tempR1=0.0
        if(tempR1.gt.1.0) tempR1=1.0
        WageNextMult(iAgg,iHFnext)=tempR1
       end do
      end do

!This piece of code computes the housing price as a function of the state.
!Note that the housing price is not directly a state variable, but it can be derived from existing state variables RP (risk premium) and Rent
!It satisfied Price(S)=Rent(S)+E[Price(Snext)]/(rf+RP(S))
      do iAgg=1,nAgg
       PH1grid(iAgg,1)=0.0
       PH2grid(iAgg,1)=0.0
      end do

      do iAge=1,100

c$omp parallel
c$omp& default(none)
c$omp& shared(iAgg,nAgg,nWage,nHF,nH2,nH1,nRP2,nRP1,nRent1,nRent2,
c$omp& deprH,PriceBond,WageNextGrid,Rent1nextGrid,H2nextGrid,
c$omp& Rent2nextGrid,H1nextGrid,RP1nextGrid,RP2nextGrid,WageGrid,
c$omp& Rent1grid,Rent2grid,H1grid,H2grid,RP1grid,RP2grid,TrProbHF,
c$omp& PH1grid,PH2grid,PH1grid0,PH2grid0,PH1nextGrid,PH2nextGrid,
c$omp& RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,NumRetired,
c$omp& PensionGrid,taxss,taxProp,iAge,PropTaxIncome,ShareOwned,
c$omp& RCavgrent,nAgent,nFirmC,nFirm1,nFirm2,taxpropOOT,HFgrid0,HFgrid1,
c$omp& ProfitRedist,ProfitGrid,RCavgrentDev)
c$omp& private(tempI1,iHF,iH2,iH1,iRP2,iRP1,iRent2,iRent1,iWage,iHFnext,
c$omp& PH1next,PH2next,EPH1next,EPH2next,HoursDemandC,
c$omp& HoursDemandLOC1,HoursDemandLOC2,ProfitC,ProfitLOC1,ProfitLOC2,
c$omp& HoursDemand,Wage,PHavg,tempR1,tempR2,tempR3,ForDemTot)
c$omp do

      do iAgg=1,nAgg
!       iAgg=(iWage-1)*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
!     1      (iRent1-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
!     1      (iRent2-1)*nRP1*nRP2*nH1*nH2*nHF+
!     1      (iRP1-1)*nRP2*nH1*nH2*nHF+
!     1      (iRP2-1)*nH1*nH2*nHF+(iH1-1)*nH2*nHF+(iH2-1)*nHF+iHF
       iHF=mod(iAgg-1,nHF)+1
       tempI1=1+(iAgg-iHF)/nHF
       iH2=mod(tempI1-1,nH2)+1
       tempI1=1+(tempI1-iH2)/nH2
       iH1=mod(tempI1-1,nH1)+1
       tempI1=1+(tempI1-iH1)/nH1
       iRP2=mod(tempI1-1,nRP2)+1
       tempI1=1+(tempI1-iRP2)/nRP2
       iRP1=mod(tempI1-1,nRP1)+1
       tempI1=1+(tempI1-iRP1)/nRP1
       iRent2=mod(tempI1-1,nRent2)+1
       tempI1=1+(tempI1-iRent2)/nRent2
       iRent1=mod(tempI1-1,nRent1)+1
       iWage=1+(tempI1-iRent1)/nRent1

       EPH1next=0
       EPH2next=0
       do iHFnext=1,nHF
        call interpAgg(PH1grid,nAgg,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     WageNextGrid(iAgg,iHFnext),Rent1nextGrid(iAgg,iHFnext),
     1     Rent2nextGrid(iAgg,iHFnext),RP1nextGrid(iAgg,iHFnext),
     1     RP2nextGrid(iAgg,iHFnext),H1nextGrid(iAgg,iHFnext),
     1     H2nextGrid(iAgg,iHFnext),iHFnext,PH1next)
        call interpAgg(PH2grid,nAgg,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     WageNextGrid(iAgg,iHFnext),Rent1nextGrid(iAgg,iHFnext),
     1     Rent2nextGrid(iAgg,iHFnext),RP1nextGrid(iAgg,iHFnext),
     1     RP2nextGrid(iAgg,iHFnext),H1nextGrid(iAgg,iHFnext),
     1     H2nextGrid(iAgg,iHFnext),iHFnext,PH2next)
        EPH1next=EPH1next+TrProbHF(iHF,iHFnext)*PH1next
        EPH2next=EPH2next+TrProbHF(iHF,iHFnext)*PH2next
        PH1nextGrid(iAgg,iHFnext)=PH1next
        PH2nextGrid(iAgg,iHFnext)=PH2next
       end do !iHFnext


       PH1grid0(iAgg,1)=Rent1Grid(iRent1)+
     1      (1.0-deprH(1)-taxProp(iHF,1))*EPH1next/
     1      ((1.0/PriceBond)+RP1grid(iRP1))
       PH2grid0(iAgg,1)=Rent2Grid(iRent2)+
     1      (1.0-deprH(2)-taxProp(iHF,2))*EPH2next/
     1      ((1.0/PriceBond)+RP2grid(iRP2))

       if(iAge.eq.100) then
        Wage=WageGrid(iWage)
        tempR1=1.0-(H1nextGrid(iAgg,1)/HBARloc1(iHF))    !Though labeled next here, this is actually H1(t), the regression is such that H1nextGrid(iAgg,1)=H1nextGrid(iAgg,2)
        tempR2=1.0-(H2nextGrid(iAgg,1)/HBARloc2(iHF))    !Though labeled next here, this is actually H2(t), the regression is such that H2nextGrid(iAgg,1)=H2nextGrid(iAgg,2)
        if(tempR1.lt.0.01) tempR1=0.01
        if(tempR2.lt.0.01) tempR2=0.01
        PHavg(1)=PH1grid0(iAgg,1)*
     1 (ShareOwned(iAgg,1)+(1.0-ShareOwned(iAgg,1))*RCavgrentDev(1,iHF))
        PHavg(2)=PH2grid0(iAgg,1)*
     1 (ShareOwned(iAgg,2)+(1.0-ShareOwned(iAgg,2))*RCavgrentDev(2,iHF))
        HoursDemandC=nFirmC*(RTSC/Wage)**(1.0/(1.0-RTSC))
        if(abs(RTSH0loc1-1.0).gt.0.0001) then
         HoursDemandLOC1=nFirm1*
     1    (tempR1*RTSH0loc1*PHavg(1)/Wage)**(1.0/(1.0-RTSH0loc1))
        else
         HoursDemandLOC1=(H1nextGrid(iAgg,1)-
     1                    (1.0-deprH(1))*H1grid(iH1))/tempR1
        end if
        if(abs(RTSH0loc2-1.0).gt.0.0001) then
         HoursDemandLOC2=nFirm2*
     1    (tempR2*RTSH0loc2*PHavg(2)/Wage)**(1.0/(1.0-RTSH0loc2))
        else
         HoursDemandLOC2=(H2nextGrid(iAgg,1)-
     1                    (1.0-deprH(2))*H2grid(iH2))/tempR2
        end if
        HoursDemand=HoursDemandC+HoursDemandLOC1+HoursDemandLOC2
        ProfitC=nFirmC*(((HoursDemandC/nFirmC)**RTSC)-
     1                 (HoursDemandC/nFirmC)*Wage)
        ProfitLOC1=nFirm1*(
     1           PHavg(1)*tempR1*((HoursDemandLOC1/nFirm1)**RTSH0loc1)-
     1          (HoursDemandLOC1/nFirm1)*Wage)
        ProfitLOC2=nFirm2*(
     1           PHavg(2)*tempR2*((HoursDemandLOC2/nFirm2)**RTSH0loc2)-
     1          (HoursDemandLOC2/nFirm2)*Wage)
        ProfitGrid(iAgg)=(ProfitRedist(1)*ProfitC+
     1                    ProfitRedist(2)*ProfitLOC1+
     1                    ProfitRedist(3)*ProfitLOC2)/real(nAgent)
!!!        PensionGrid(iAgg)=HoursDemand*Wage*taxss/NumRetired

        ForDemTot(1)=exp(HFgrid0(iHF,1)-
     1                   HFgrid1(iHF,1)*
     1                   log(PH1grid0(iAgg,1)*(1.0+taxpropOOT(1))))    !Foreign Demand per Household in Z1
        ForDemTot(2)=exp(HFgrid0(iHF,2)-
     1                   HFgrid1(iHF,2)*
     1                   log(PH2grid0(iAgg,1)*(1.0+taxpropOOT(2))))    !Foreign Demand per Household in Z2
        PropTaxIncome(iAgg)=taxprop(iHF,1)*H1grid(iH1)*PH1grid0(iAgg,1)+
     1                      taxprop(iHF,2)*H2grid(iH2)*PH2grid0(iAgg,1)+
     1                      taxpropOOT(1)*ForDemTot(1)*PH1grid0(iAgg,1)+
     1                      taxpropOOT(2)*ForDemTot(2)*PH2grid0(iAgg,1)       !Property Tax Income per capita
       end if

      end do !iAgg

c$omp end do
c$omp end parallel

      do iAgg=1,nAgg
       PH1grid(iAgg,1)=PH1grid0(iAgg,1)
       PH2grid(iAgg,1)=PH2grid0(iAgg,1)
       if(PH1grid(iAgg,1).lt.0) PH1grid(iAgg,1)=0
       if(PH2grid(iAgg,1).lt.0) PH2grid(iAgg,1)=0
      end do

      end do  !iAge

      call writedata(PH1grid,'Price1.txt',nAgg,1,nAgg,1)
      call writedata(PH2grid,'Price2.txt',nAgg,1,nAgg,1)


!initialize value function
      do iAgg=1,nAgg
      do iRClast=1,nRClast
      do iDZ=1,nDZ
      do iNW=1,nNW
       iInd=(iRClast-1)*nDZ*nNW+(iDZ-1)*nNW+iNW
       iState=(iInd-1)*nAgg+iAgg
       ValFun(iState,1)=0.0
       if(NWgridAll((1-1)*nDZ+iDZ,iNW).lt.0.0) then
        ValFun(iState,1)=MinVal*(0.1-NWgridAll((1-1)*nDZ+iDZ,iNW)/10.0)
       end if
!      ValFun(iState,1)=((NWgrid(iNW)-NWgrid(1)+.01)**(1.0-gamma0))/
!     1   (1.0-gamma0)
      end do
      end do
      end do
      end do

!!!valXX.txt is used to compute iAge=nAge+2-XX
      tempI1=0
      if(tempI1.eq.1) then
      call readdatabinary(ValFunCond,'val10.dat',nAgg*nInd,
     1                     (2+nRC)*nLOC+1)
      do iState=1,nAgg*nInd
       ValFun(iState,1)=ValFunCond(iState,(2+nRC)*nLOC+1)
      end do
      end if

      do iAge=1,nAge

      flagRet=1
      if(iAge.le.nRet) flagRet=2

c$omp parallel
c$omp& default(none)
c$omp& shared(iAgg,nAgg,nDZ,nNW,nHF,nH2,nH1,nRP2,nRP1,nRent1,nRent2,
c$omp& WageNextSpot,WageNextMult,Rent1nextSpot,Rent1nextMult,H2nextSpot,
c$omp& Rent2nextSpot,Rent2nextMult,H1nextSpot,H1nextMult,H2nextMult,
c$omp& RP1nextSpot,RP1nextMult,RP2nextSpot,RP2nextMult,ValFunNext,
c$omp& ValFun,NWgridAll,BeqGrid,BeqProb,iAge,nAge,nBeqDist,BeqDist,
c$omp& fracBeq,nRClast)
c$omp& private(tempI1,iHF,iH2,iH1,iRP2,iRP1,iRent2,iRent1,iWage,iHFnext,
c$omp& iNWnext,iWageNext,iH1next,iH2next,iRP1next,iRP2next,iRent1next,
c$omp& iRent2next,iIndNext,iDZnext,NWnextBeqRec,iIndNextBeqRec,
c$omp& multWage,multH1,multH2,multRP1,multRP2,multNWnextBeqRec,
c$omp& multRent1,multRent2,jH1,jH2,jWage,jRent1,
c$omp& jRent2,jRP1,jRP2,iAggNext,Vnext,Vnext1,VnextBeqRec,
c$omp& Vnext2,Vnext3,Vnext4,Vnext5,Vnext6,Vnext7,Vnext1beq,
c$omp& Vnext7beq,Vnext6beq,Vnext5beq,Vnext4beq,Vnext3beq,Vnext2beq,
c$omp& iStateNext,NWgridNext,tempR1,iRClastNext)
c$omp do
!This speeds up the dynamic program. Consider an agent whose current aggregate state is iAgg.
!From the aggregate state we know next period's aggregate state iAggNext, as a function of the shocks. Compute
!V(iAggNext,NWnext) over a range of NWnext. This quantity interpolates out the aggregate state. Note that interpolation is
!irrelevant if the grid was fine enough. However, none of the choice or expectations are done at this stage. The choice and
!expectation over realized shocks is done in the main part of the code (below). The benefit of this speed up is that
!the main part of the code below does not need to interpolate over the aggregate state, as its all done ahead of time, here.
      do iAgg=1,nAgg
       iHF=mod(iAgg-1,nHF)+1
       tempI1=1+(iAgg-iHF)/nHF
       iH2=mod(tempI1-1,nH2)+1
       tempI1=1+(tempI1-iH2)/nH2
       iH1=mod(tempI1-1,nH1)+1
       tempI1=1+(tempI1-iH1)/nH1
       iRP2=mod(tempI1-1,nRP2)+1
       tempI1=1+(tempI1-iRP2)/nRP2
       iRP1=mod(tempI1-1,nRP1)+1
       tempI1=1+(tempI1-iRP1)/nRP1
       iRent2=mod(tempI1-1,nRent2)+1
       tempI1=1+(tempI1-iRent2)/nRent2
       iRent1=mod(tempI1-1,nRent1)+1
       iWage=1+(tempI1-iRent1)/nRent1

       do iHFnext=1,nHF
        iWageNext=WageNextSpot(iAgg,iHFnext)
        iRent1next=Rent1nextSpot(iAgg,iHFnext)
        iRent2next=Rent2nextSpot(iAgg,iHFnext)
        iRP1next=RP1nextSpot(iAgg,iHFnext)
        iRP2next=RP2nextSpot(iAgg,iHFnext)
        iH1next=H1nextSpot(iAgg,iHFnext)
        iH2next=H2nextSpot(iAgg,iHFnext)
        multWage=WageNextMult(iAgg,iHFnext)
        multRent1=Rent1nextMult(iAgg,iHFnext)
        multRent2=Rent2nextMult(iAgg,iHFnext)
        multRP1=RP1nextMult(iAgg,iHFnext)
        multRP2=RP2nextMult(iAgg,iHFnext)
        multH1=H1nextMult(iAgg,iHFnext)
        multH2=H2nextMult(iAgg,iHFnext)

        do iDZnext=1,nDZ

        do iNWnext=1,nNW
         if(iAge.eq.1) then
          NWgridNext(iNWnext)=
     1      NWgridAll((nAge+1-iAge-1)*nDZ+iDZnext,iNWnext)
         else
          NWgridNext(iNWnext)=
     1      NWgridAll((nAge+2-iAge-1)*nDZ+iDZnext,iNWnext) !When  solving 19 year old's (iAge=2) problem, need to use ValFun and NWgrid of 20 year old
         end if
        end do

        do iRClastNext=1,nRClast
        do iNWnext=1,nNW
         iIndNext=(iRClastNext-1)*nDZ*nNW+(iDZnext-1)*nNW+iNWnext

         do iBeqDist=1,nBeqDist
!          NWnextBeqRec(iBeqDist)=NWgridNext(iNWnext)+
!     1                           BeqGrid(iAgg,iHFnext)
          if(fracBeq.lt.0.0001) then
           tempI1=0
          else
           tempI1=0
           if(iDZnext.gt.nDZ/2) tempI1=nBeqDist
          end if
          NWnextBeqRec(iBeqDist)=NWgridNext(iNWnext)+
     1                           BeqDist(iAgg,iHFnext,tempI1+iBeqDist)
          call findspot(NWgridNext,nNW,NWnextBeqRec(iBeqDist),
     1                  nint(0.5*real(nNW)),tempI1)
          iIndNextBeqRec(iBeqDist)=
     1             (iRClastNext-1)*nDZ*nNW+(iDZnext-1)*nNW+tempI1
          multNWnextBeqRec(iBeqDist)=
     1     (NWnextBeqRec(iBeqDist)-NWgridNext(tempI1))/
     1     (NWgridNext(tempI1+1)-NWgridNext(tempI1))
          if(multNWnextBeqRec(iBeqDist).lt.0.0) then
           multNWnextBeqRec(iBeqDist)=0.0
          end if
          if(multNWnextBeqRec(iBeqDist).gt.1.0) then
           multNWnextBeqRec(iBeqDist)=1.0
          end if
         end do

         do jWage=1,2
          do jRent1=1,2
           do jRent2=1,2
            do jRP1=1,2
             do jRP2=1,2
              do jH1=1,2
               do jH2=1,2
                iAggNext=(iWageNext+(jWage-1)-1)*
     1                            nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1           (iRent1next+(jRent1-1)-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1           (iRent2next+(jRent2-1)-1)*nRP1*nRP2*nH1*nH2*nHF+
     1           (iRP1next+(jRP1-1)-1)*nRP2*nH1*nH2*nHF+
     1           (iRP2next+(jRP2-1)-1)*nH1*nH2*nHF+
     1           (iH1next+(jH1-1)-1)*nH2*nHF+
     1           (iH2next+(jH2-1)-1)*nHF+iHFnext
                iStateNext=(iIndNext-1)*nAgg+iAggNext
                Vnext7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1                ValFun(iStateNext,1)
                do iBeqDist=1,nBeqDist
                 tempI1=(iIndNextBeqRec(iBeqDist)-1)*nAgg+iAggNext
                 Vnext7beq(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2,
     1                     iBeqDist)=
     1             ValFun(tempI1,1)+multNWnextBeqRec(iBeqDist)*
     1            (ValFun(tempI1+nAgg,1)-ValFun(tempI1,1))
                end do
               end do    !jH2
               Vnext6(jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1            Vnext7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1           (Vnext7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1            Vnext7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
               do iBeqDist=1,nBeqDist
                Vnext6beq(jWage,jRent1,jRent2,jRP1,jRP2,jH1,iBeqDist)=
     1          Vnext7beq(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1,iBeqDist)+
     1          multH2*
     1         (Vnext7beq(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2,iBeqDist)-
     1          Vnext7beq(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1,iBeqDist))
               end do
              end do    !jH1
              Vnext5(jWage,jRent1,jRent2,jRP1,jRP2)=
     1          Vnext6(jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1         (Vnext6(jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1          Vnext6(jWage,jRent1,jRent2,jRP1,jRP2,1))
              do iBeqDist=1,nBeqDist
               Vnext5beq(jWage,jRent1,jRent2,jRP1,jRP2,iBeqDist)=
     1          Vnext6beq(jWage,jRent1,jRent2,jRP1,jRP2,1,iBeqDist)+
     1          multH1*
     1         (Vnext6beq(jWage,jRent1,jRent2,jRP1,jRP2,2,iBeqDist)-
     1          Vnext6beq(jWage,jRent1,jRent2,jRP1,jRP2,1,iBeqDist))
              end do
             end do   !jRP2
             Vnext4(jWage,jRent1,jRent2,jRP1)=
     1         Vnext5(jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1        (Vnext5(jWage,jRent1,jRent2,jRP1,2)-
     1         Vnext5(jWage,jRent1,jRent2,jRP1,1))
             do iBeqDist=1,nBeqDist
              Vnext4beq(jWage,jRent1,jRent2,jRP1,iBeqDist)=
     1         Vnext5beq(jWage,jRent1,jRent2,jRP1,1,iBeqDist)+multRP2*
     1        (Vnext5beq(jWage,jRent1,jRent2,jRP1,2,iBeqDist)-
     1         Vnext5beq(jWage,jRent1,jRent2,jRP1,1,iBeqDist))
             end do
            end do  !jRP1
            Vnext3(jWage,jRent1,jRent2)=
     1        Vnext4(jWage,jRent1,jRent2,1)+multRP1*
     1       (Vnext4(jWage,jRent1,jRent2,2)-
     1        Vnext4(jWage,jRent1,jRent2,1))
            do iBeqDist=1,nBeqDist
             Vnext3beq(jWage,jRent1,jRent2,iBeqDist)=
     1        Vnext4beq(jWage,jRent1,jRent2,1,iBeqDist)+multRP1*
     1       (Vnext4beq(jWage,jRent1,jRent2,2,iBeqDist)-
     1        Vnext4beq(jWage,jRent1,jRent2,1,iBeqDist))
            end do
           end do !jRent2
           Vnext2(jWage,jRent1)=Vnext3(jWage,jRent1,1)+multRent2*
     1           (Vnext3(jWage,jRent1,2)-Vnext3(jWage,jRent1,1))
           do iBeqDist=1,nBeqDist
            Vnext2(jWage,jRent1)=Vnext3beq(jWage,jRent1,1,iBeqDist)+
     1                           multRent2*
     1                          (Vnext3beq(jWage,jRent1,2,iBeqDist)-
     1                           Vnext3beq(jWage,jRent1,1,iBeqDist))
           end do
          end do !jRent1
          Vnext1(jWage)=Vnext2(jWage,1)+multRent1*
     1                 (Vnext2(jWage,2)-Vnext2(jWage,1))
            if(multRent2.le.multRent1) then
             Vnext1(jWage)=
     1         Vnext3(jWage,1,1)*(1.0-multRent1)+
     1         Vnext3(jWage,2,2)*multRent2+
     1         Vnext3(jWage,2,1)*(multRent1-multRent2)
             do iBeqDist=1,nBeqDist
              Vnext1beq(jWage,iBeqDist)=
     1         Vnext3beq(jWage,1,1,iBeqDist)*(1.0-multRent1)+
     1         Vnext3beq(jWage,2,2,iBeqDist)*multRent2+
     1         Vnext3beq(jWage,2,1,iBeqDist)*(multRent1-multRent2)
             end do
            else
             Vnext1(jWage)=
     1         Vnext3(jWage,1,1)*(1.0-multRent2)+
     1         Vnext3(jWage,2,2)*multRent1+
     1         Vnext3(jWage,1,2)*(multRent2-multRent1)
             do iBeqDist=1,nBeqDist
             Vnext1beq(jWage,iBeqDist)=
     1         Vnext3beq(jWage,1,1,iBeqDist)*(1.0-multRent2)+
     1         Vnext3beq(jWage,2,2,iBeqDist)*multRent1+
     1         Vnext3beq(jWage,1,2,iBeqDist)*(multRent2-multRent1)
             end do
            end if
         end do !jWage
         Vnext=Vnext1(1)+multWage*(Vnext1(2)-Vnext1(1))
!To model heterogeneity in bequests, we partition bequest distribution into nBeqDist equally probable pieces. If an agent lands in a piece, he receives the average bequest in that piece. As nDist->inf, this resembles the actual distribution
!tempR1 contains the expected continuation value conditional on receiving a bequest. The expectation is over all possible realizations of iBeqDist
         tempR1=0.0
         do iBeqDist=1,nBeqDist
          VnextBeqRec(iBeqDist)=Vnext1beq(1,iBeqDist)+multWage*
     1               (Vnext1beq(2,iBeqDist)-Vnext1beq(1,iBeqDist))
          tempR1=tempR1+VnextBeqRec(iBeqDist)*(1.0/real(nBeqDist))
         end do
!BeqProb(1) is the probability that an agent receives a bequest before he is born
!BeqProb(2) is the probability that an agent receives a bequest after age 1 and before age 2
!BeqProb(nAge) is the probability that an agent receives a bequest after age nAge-1 and before age nAge
         if(iAge.gt.1) then
          ValFunNext((iIndNext-1)*nAgg+iAgg,iHFnext)=
     1      Vnext*(1.0-BeqProb(nAge-iAge+2))+
     1      tempR1*BeqProb(nAge-iAge+2)
         else
          ValFunNext((iIndNext-1)*nAgg+iAgg,iHFnext)=Vnext
         end if
        end do  !iNWnext
        end do  !iRClastNext
        end do  !iDZnext
       end do   !iHFnext

      end do !iAgg

c$omp end do
c$omp end parallel

c$omp parallel
c$omp& default(none)
c$omp& shared(iAgg,nAgg,nHF,nNW,nRClast,nDZ,NWgridAll,
c$omp& ValFunNext,dValFunNext,iAge,nAge)
c$omp& private(iNWnext,iState,ValFunNW,dValFunNW,tempI1,tempI2,
c$omp& iHFnext,iDZnext,iInd,NWgridNext,iRClastNext)
c$omp do
!compute derivatives of value function
      do iAgg=1,nAgg
      do iHFnext=1,nHF
      do iRClastNext=1,nRClast
      do iDZnext=1,nDZ
       do iNWnext=1,nNW
        if(iAge.eq.1) then
         NWgridNext(iNWnext)=
     1      NWgridAll((nAge+1-iAge-1)*nDZ+iDZnext,iNWnext)
        else
         NWgridNext(iNWnext)=
     1      NWgridAll((nAge+2-iAge-1)*nDZ+iDZnext,iNWnext) !When  solving 19 year old's (iAge=2) problem, need to use ValFun and NWgrid of 20 year old
        end if
        iInd=(iRClastNext-1)*nDZ*nNW+(iDZnext-1)*nNW+iNWnext
        iState=(iInd-1)*nAgg+iAgg
        ValFunNW(iNWnext)=ValFunNext(iState,iHFnext)
       end do
       tempI1=1
       tempI2=0
       call PCHIM(nNW,NWgridNext,ValFunNW,dValFunNW,tempI1,tempI2)
       do iNWnext=1,nNW
        iInd=(iRClastNext-1)*nDZ*nNW+(iDZnext-1)*nNW+iNWnext
        iState=(iInd-1)*nAgg+iAgg
        dValFunNext(iState,iHFnext)=dValFunNW(iNWnext)
       end do
      end do
      end do
      end do
      end do

c$omp end do
c$omp end parallel

c$omp parallel
c$omp& default(none)
c$omp& shared(iAgg,nAgg,nNW,nHF,nH2,nH1,nRP2,nRP1,nRent1,nRent2,nDZ,
c$omp& nLOC,TrProbHF,TrProbDZ,alphaN,alphaC,alphaH,thetaRes,thetaInv,
c$omp& gamma0,ValFunNext,dValFunNext,DZgrid,Rent1grid,Rent2grid,param0,
c$omp& RP1grid,RP2grid,WageGrid,Policy,iAge,CchoiceGrid0,HchoiceGrid0,
c$omp& Rent1nextGrid,Rent2nextGrid,RP1nextGrid,RP2nextGrid,CommCost,
c$omp& nCchoiceTemp0,nCchoiceTemp1,nHchoiceTemp0,nHchoiceTemp1,MinVal,
c$omp& deprH,deprINV0,beta0,ValFun0,PriceBond,nRet,PensionGrid,nAge,
c$omp& AgeProd,ValFunCond,VA,QA,PH1grid,PH2grid,PH1nextGrid,PH2nextGrid,
c$omp& ProbDeath,taxss,taxprop,BeqGrid,BeqProb,SSIdist,LeisureMin,
c$omp& CommCostFin,PropTaxIncome,HresMin,CluxCut,CluxCost,flagRet,NWmin,
c$omp& RCrentred,RChsize,RCprob,RCinccut,nRC,RCavgrent,WageNextGrid,
c$omp& Z1shiftSize,Z1shiftCut,H1nextGrid,H2nextGrid,nInd,NWgridAll,
c$omp& BeqStrength,BeqLux,UncondDistDZ,nDepr,DeprProb,DeprGrid,BetaRel,
c$omp& DeathExp,PubGood,ProfitGrid,ElastCH,ElastCN,param1,param2,
c$omp& chi0,HoursMin,r0,lambda0,tau0,lambdaBase,tauBase,Z1shiftAll,
c$omp& nRClast,RCprobStay,flagRCstay)
c$omp& private(iNW,iState,tempI1,iHF,iH2,iH1,iRP2,iRP1,iRent2,iRent1,
c$omp& iWage,iLOC,iDZ,iHFnext,iCchoice,iHchoice,iNWnext,nHchoiceTemp,V,
c$omp& iStateNextL,iStateNextH,iRenter,Wage,Rent,PH,Bnext,PHnext,
c$omp& CchoiceMin0,CchoiceMax0,CchoiceMin1,CchoiceMax1,CchoiceMin2,Cint,
c$omp& CchoiceMax2,HchoiceMin0,HchoiceMax0,HchoiceMin1,HchoiceMax1,
c$omp& HchoiceMin2,HchoiceMax2,CchoiceMin,CchoiceMax,HchoiceMin,NWnext,
c$omp& HchoiceMax,Cchoice,Hchoice,NW,Hours,Hres,Util,Vmax,EVnext,TrProb,
c$omp& Vnext,extrap,LaborIncome,iChoiceDisc,VmaxCond,PHnextMin,iDZnext,
c$omp& iInd,Normalize,iIndNext,iDepr,EvnextBeq,TrProbDepr,RCprobTemp,
c$omp& CluxCost0,NWgrid,NWgridNext,UtilPubGood,LaborIncomePreTax,
c$omp& HchoiceUppBound,flagUppBound,tempR1,tempR2,tempR3,CommCostTemp,
c$omp& HoursConst0,HoursConst1,HouseConst0,HouseConst1,HouseConst2,
c$omp& UtilConst0,UtilConst1,UtilConst2,Pension,HoursConst2,HoursConst3,
c$omp& HoursGrid,HoursGrid0,flagMinVal,iHoursChoice,TaxableIncome,
c$omp& HSVtax,HSVtaxBase,HresMinVoucher,iRClast,iRClastNext)
c$omp do
!Tis is the main part of the code. Here we go through possible location, consumption, and residential investment choices and find the optimal one
      do iAgg=1,nAgg!2187,2187!1,nAgg
       iHF=mod(iAgg-1,nHF)+1
       tempI1=1+(iAgg-iHF)/nHF
       iH2=mod(tempI1-1,nH2)+1
       tempI1=1+(tempI1-iH2)/nH2
       iH1=mod(tempI1-1,nH1)+1
       tempI1=1+(tempI1-iH1)/nH1
       iRP2=mod(tempI1-1,nRP2)+1
       tempI1=1+(tempI1-iRP2)/nRP2
       iRP1=mod(tempI1-1,nRP1)+1
       tempI1=1+(tempI1-iRP1)/nRP1
       iRent2=mod(tempI1-1,nRent2)+1
       tempI1=1+(tempI1-iRent2)/nRent2
       iRent1=mod(tempI1-1,nRent1)+1
       iWage=1+(tempI1-iRent1)/nRent1
       Wage=WageGrid(iWage)
       Rent(1)=Rent1grid(iRent1)
       Rent(2)=Rent2grid(iRent2)
       PH(1)=PH1grid(iAgg,1)
       PH(2)=PH2grid(iAgg,1)
       Normalize=1.0
!       UtilPubGood=(PubGood/(1.0-gamma0))*
!     1             (PropTaxIncome(iAgg)**((1.0-gamma0)*(alphaC+alphaH)))
       UtilPubGood=exp((1-gamma0)*PubGood*PropTaxIncome(iAgg))

       PHnextMin(1)=100000
       PHnextMin(2)=100000
       do iHFnext=1,nHF
        if(PH1nextGrid(iAgg,iHFnext).lt.PHnextMin(1)) then
         PHnextMin(1)=PH1nextGrid(iAgg,iHFnext)
        end if
        if(PH2nextGrid(iAgg,iHFnext).lt.PHnextMin(2)) then
         PHnextMin(2)=PH2nextGrid(iAgg,iHFnext)
        end if
       end do

      do iRClast=1,nRClast
      do iDZ=1,nDZ

       HoursConst0=((1.0-taxss)*DZgrid(nAge+1-iAge,iDZ)*
     1           Wage*AgeProd(nAge+1-iAge))**(-1.0/(1.0-chi0*ElastCN))
       if(iAge.le.nRet) then
        Pension=SSIdist(iDZ)*PensionGrid(iAgg)
       else
        Pension=0.0
       end if

      tempI1=0
      if(iRClast.eq.1.or.
     1  (iRClast.eq.2.and.iRenter.eq.3.and.iLOC.eq.1).or.
     1  (iRClast.eq.3.and.iRenter.eq.3.and.iLOC.eq.2)) tempI1=1
      if(tempI1.eq.1) then
      do iNW=1,nNW
       iInd=(iRClast-1)*nDZ*nNW+(iDZ-1)*nNW+iNW
       iState=(iInd-1)*nAgg+iAgg
       NWgrid(iNW)=NWgridAll((nAge+1-iAge-1)*nDZ+iDZ,iNW)
       do iChoiceDisc=1,nLOC*(2+nRC)
        Policy(iState,(iChoiceDisc-1)*2+1)=0.01
        Policy(iState,(iChoiceDisc-1)*2+2)=0.01
        ValFunCond(iState,iChoiceDisc)=-10.0
       end do
!If NWgridAll does not depend on (iAge,iDZ) can define NWgridNext here, otherwise must be later in code
       if(iAge.eq.1) then
        NWgridNext(iNW)=
     1   NWgridAll((nAge+1-iAge-1)*nDZ+1,iNW)
       else
        NWgridNext(iNW)=
     1   NWgridAll((nAge+2-iAge-1)*nDZ+1,iNW) !When  solving 19 year old's (iAge=2) problem, need to use ValFun and NWgrid of 20 year old
       end if
      end do
      end if

      do iNW=1,nNW

      if(UncondDistDZ(1,iDZ).lt.0.00001) goto 9871
       Vmax=10*MinVal
       VmaxCond=10*MinVal
       iInd=(iRClast-1)*nDZ*nNW+(iDZ-1)*nNW+iNW
       iState=(iInd-1)*nAgg+iAgg
!iRClast=1 -> not in RC last period; iRClast=2,3 -> in RC last period.
!Conditional on each descrete choice (iLOC,iRenter), the policy and value function of all iRClast agents is identical.
!This is why this is solved for iRClast=1 only and code jumps to 9871 for others.
!The only difference across iRClast agents is probability of receiving some of these discrete choices, which leads to different unconditional value function. This is computed after line 9871
       NW=NWgrid(iNW)

       do iRenter=1,2+nRC
       do iLOC=1,nLOC
       
        tempI1=0
        if(iRClast.eq.1.or.
     1     (iRClast.eq.2.and.iRenter.eq.3.and.iLOC.eq.1).or.
     1     (iRClast.eq.3.and.iRenter.eq.3.and.iLOC.eq.2)) tempI1=1
        if(tempI1.eq.0) goto 9869
       
        VmaxCond=10*MinVal
        iChoiceDisc=(iRenter-1)*nLOC+iLOC
        if(iRenter.ne.2+nRC.or.nRClast.eq.1) then
         iRClastNext=1      !non-RC household
        else
         iRClastNext=1+iLOC !RC household in Z1 or Z2
        end if
        if(abs(ElastCH).gt.0.0001) then
         HoursConst1=(alphaC+alphaH*
     1   ((alphaH/(alphaC*Rent(iLOC)))**(elastCH/(1.0-elastCH))))**
     1   ((ElastCH-ElastCN)/(ElastCH*(1.0-chi0*ElastCN)))
        else
         HoursConst1=(alphaC*Rent(iLOC)/alphaH)**
     1               (alphaH*ElastCN/(1.0-chi0*ElastCN))
        end if
        HouseConst0=(alphaH/(alphaC*Rent(iLOC)))
        HouseConst1=HouseConst0/(1.0-RCrentred(iLOC,iHF))
        HouseConst2=HouseConst0*
     1  (1.0-deprH(iLOC)-taxProp(iHF,iLOC)-deprINV0)/
     1  (1.0-deprH(iLOC)-taxProp(iHF,iLOC)-deprINV0*PH(iLOC)/Rent(iLOC))
!Uncomment this for model w/ owners only
!        if(iRenter.ne.2) then
!         ValFunCond(iState,iChoiceDisc)=MinVal
!         goto 9869
!        end if

!This piece of code is used to search for optimal hours given consumption through the non-linear equation relating the two
!It creates HoursGrid where 1st column is guess for hours and 2nd is associated consumption
!Further below the grid will be updated to zoom in on each consumption choice and find the associated hours
        if(iRenter.ne.3) then
         tempR1=Rent(iLOC)
        else
         tempR1=Rent(iLOC)*(1.0-RCrentred(iLOC,iHF))
        end if
        HoursConst2=(alphaC+alphaH*
     1    ((alphaH/(alphaC*tempR1))**(elastCH/(1.0-elastCH))))**
     1    ((ElastCN-ElastCH)/ElastCH)
        HoursConst3=DZgrid(nAge+1-iAge,iDZ)*Wage*AgeProd(nAge+1-iAge)*
     1              HoursConst2*(1.0-alphaN)*(1.0-alphaH)/(chi0*alphaN)
        tempR1=0.0 !hours guess
        tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1   ((r0*NW+ProfitGrid(iAgg)+tempR1*
     1     DZgrid(nAge+1-iAge,iDZ)*Wage*
     1     AgeProd(nAge+1-iAge))**(-tau0(iHF)))
        tempR3=(1.0-LeisureMin-CommCost(iLOC,flagRet)-tempR1)**
     1         (chi0*elastCN-1.0)
        HoursGrid0(1,1)=tempR1
        HoursGrid0(1,2)=(HoursConst3*tempR2/tempR3)**(1.0/(1.0-elastCN))  !consumption given hours guess
        tempR1=0.5 !hours guess
        tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1   ((r0*NW+ProfitGrid(iAgg)+tempR1*
     1     DZgrid(nAge+1-iAge,iDZ)*Wage*
     1     AgeProd(nAge+1-iAge))**(-tau0(iHF)))
        tempR3=(1.0-LeisureMin-CommCost(iLOC,flagRet)-tempR1)**
     1         (chi0*elastCN-1.0)
        HoursGrid0(2,1)=tempR1
        HoursGrid0(2,2)=(HoursConst3*tempR2/tempR3)**(1.0/(1.0-elastCN))  !consumption given hours guess
        tempR1=1.0-LeisureMin-CommCost(iLOC,flagRet)-0.01 !hours guess
        tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1   ((r0*NW+ProfitGrid(iAgg)+tempR1*
     1     DZgrid(nAge+1-iAge,iDZ)*Wage*
     1     AgeProd(nAge+1-iAge))**(-tau0(iHF)))
        tempR3=(1.0-LeisureMin-CommCost(iLOC,flagRet)-tempR1)**
     1         (chi0*elastCN-1.0)
        HoursGrid0(3,1)=tempR1
        HoursGrid0(3,2)=(HoursConst3*tempR2/tempR3)**(1.0/(1.0-elastCN))  !consumption given hours guess

        ValFunCond(iState,iChoiceDisc)=VmaxCond*1.2
        CchoiceMin0=CchoiceGrid0(1)
        CchoiceMax0=CchoiceGrid0(nCchoice0)
        HchoiceMin0=HchoiceGrid0(1)
        HchoiceMax0=HchoiceGrid0(nHchoice0)
        CchoiceMin1=CchoiceGrid0(1)
        CchoiceMax1=CchoiceGrid0(nCchoice0)
        HchoiceMin1=HchoiceGrid0(1)
        HchoiceMax1=HchoiceGrid0(nHchoice0)
        CchoiceMin2=CchoiceGrid0(1)
        CchoiceMax2=CchoiceGrid0(nCchoice0)
        HchoiceMin2=HchoiceGrid0(1)
        HchoiceMax2=HchoiceGrid0(nHchoice0)

       do iCchoice=1,nCchoice0+1+nCchoice1+nCchoice2+nCchoice3

        flagMinVal=0
        flagUppBound=0
        if(iCchoice.le.nCchoice0+1) then
         if(iAge.le.nRet) then
          LaborIncome=PensionGrid(iAgg)+
     1                1.0*Wage*AgeProd(nAge+1-iAge)*(1.0-taxss)
         else
          LaborIncome=1.0*Wage*AgeProd(nAge+1-iAge)*(1.0-taxss)
         end if
         tempR1=NWgrid(iNW)
         if(tempR1.lt.0.01) tempR1=0.01
         CchoiceMin=0.001
         CchoiceMax=(tempR1+LaborIncome)*1.05+0.05
         Cint=(CchoiceMax-CchoiceMin)/real(nCchoice0)
         if(Cint.lt.0.05) Cint=0.05
        end if
        if(iCchoice.eq.nCchoice0+1+1) then
         CchoiceMin=CchoiceMin0
         CchoiceMax=CchoiceMax0
         HchoiceMin=HchoiceMin0
         HchoiceMax=HchoiceMax0
        end if
        if(iCchoice.eq.nCchoice0+1+nCchoice1+1) then
         CchoiceMin=CchoiceMin1
         CchoiceMax=CchoiceMax1
         HchoiceMin=HchoiceMin1
         HchoiceMax=HchoiceMax1
        end if
        if(iCchoice.eq.nCchoice0+1+nCchoice1+nCchoice2+1) then
         CchoiceMin=CchoiceMin2
         CchoiceMax=CchoiceMax2
         HchoiceMin=HchoiceMin2
         HchoiceMax=HchoiceMax2
        end if

        if(iCchoice.le.nCchoice0) then
         !Cchoice=CchoiceGrid0(iCchoice)
         tempR1=real(iCchoice-1)/real(nCchoice0-1)
         Cchoice=CchoiceMin+(CchoiceMax-CchoiceMin)*tempR1
         nHchoiceTemp=nHchoice0
        else
         if(iCchoice.eq.nCchoice0+1) then
          if(iNW.gt.1) then
           Cchoice=Policy(iState-nAgg,(iChoiceDisc-1)*2+1)
           nHchoiceTemp=1
          else
           Cchoice=0.001
           nHchoiceTemp=1
          end if
         else
          tempR1=real(iCchoice-nCchoiceTemp0(iCchoice)-1)/
     1           real(nCchoiceTemp1(iCchoice)-1)
          Cchoice=CchoiceMin+(CchoiceMax-CchoiceMin)*tempR1
          if(iCchoice.eq.nCchoice0+1+1) nHchoiceTemp=nHchoice1
          if(iCchoice.eq.nCchoice0+1+nCchoice1+1) nHchoiceTemp=nHchoice2
          if(iCchoice.eq.nCchoice0+1+nCchoice1+nCchoice2+1)
     1       nHchoiceTemp=nHchoice3
         end if
        end if
        CluxCost0=0.0
        if(iLOC.eq.2.and.Cchoice.gt.CluxCut(flagRet)) then
         CluxCost0=CluxCost(flagRet)*(Cchoice-CluxCut(flagRet))
        end if
        
        if(abs(tau0(iHF)).lt.0.00001.and.
     1     abs(lambda0(iHF)-1.0).lt.0.00001) then
!!old way of computing hours - works if HSV tax is zero
!!param1=((chi0*alphaN/(alphaC*(1.0-alphaN)))**(1.0/(1.0-chi0*ElastCN)))
!!HoursConst0=((1.0-taxss)*DZgrid(nAge+1-iAge,iDZ)*Wage*AgeProd(nAge+1-iAge))**(-1.0/(1.0-chi0*ElastCN))
!!HoursConst1=(1.0-alphaH+alphaH*((alphaH/((1.0-alphaH)*Rent(iLOC)))**(elastCH/(1.0-elastCH)))**((ElastCH-ElastCN)/(ElastCH*(1.0-chi0*ElastCN)))
         Hours=1.0-LeisureMin-CommCost(iLOC,flagRet)-
     1         (Cchoice**param2)*param1*HoursConst0*HoursConst1
         if(iLOC.eq.2.and.Cchoice.gt.CluxCut(flagRet)) then
          Hours=1.0-LeisureMin-CommCost(iLOC,flagRet)-
     1          (Cchoice**param2)*param1*HoursConst0*HoursConst1*
     1         (1.0+CluxCost(flagRet))
         end if
        else
!!new way of computing hours - works if HSV tax >=0. searches for solution of nonlinear equation relating C to N
         do tempI1=1,3
         do tempI2=1,2
          HoursGrid(tempI1,tempI2)=HoursGrid0(tempI1,tempI2)
         end do
         end do
         do iHoursChoice=1,7
          if(abs(Cchoice-0.5*(HoursGrid(1,2)+HoursGrid(2,2))).lt.
     1       abs(Cchoice-0.5*(HoursGrid(2,2)+HoursGrid(3,2)))) then
           HoursGrid(3,1)=HoursGrid(2,1)
           HoursGrid(3,2)=HoursGrid(2,2)
           HoursGrid(2,1)=0.5*(HoursGrid(1,1)+HoursGrid(2,1))
          else
           HoursGrid(1,1)=HoursGrid(2,1)
           HoursGrid(1,2)=HoursGrid(2,2)
           HoursGrid(2,1)=0.5*(HoursGrid(2,1)+HoursGrid(3,1))
          end if
          tempR1=HoursGrid(2,1)
          tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1    ((r0*NW+ProfitGrid(iAgg)+tempR1*
     1      DZgrid(nAge+1-iAge,iDZ)*Wage*
     1      AgeProd(nAge+1-iAge))**(-tau0(iHF)))
          tempR3=(1.0-LeisureMin-CommCost(iLOC,flagRet)-tempR1)**
     1           (chi0*elastCN-1.0)
          HoursGrid(2,2)=(HoursConst3*tempR2/tempR3)**
     1                   (1.0/(1.0-elastCN))
         end do
         if(abs(Cchoice-0.5*(HoursGrid(1,2)+HoursGrid(2,2))).lt.
     1      abs(Cchoice-0.5*(HoursGrid(2,2)+HoursGrid(3,2)))) then
          tempR1=(Cchoice-HoursGrid(1,2))/
     1           (HoursGrid(2,2)-HoursGrid(1,2))
          Hours=HoursGrid(1,1)+tempR1*(HoursGrid(2,1)-HoursGrid(1,1))
         else
          tempR1=(Cchoice-HoursGrid(2,2))/
     1           (HoursGrid(3,2)-HoursGrid(2,2))
          Hours=HoursGrid(2,1)+tempR1*(HoursGrid(3,1)-HoursGrid(2,1))
         end if
!end new way of computing hours
        end if

        if(Hours.lt.HoursMin.and.iAge.gt.nRet) Hours=HoursMin
        CommCostTemp=CommCostFin(iLOC,flagRet)
        if(iAge.le.nRet) then
         Hours=0.0
         CommCostTemp=CommCostFin(iLOC,2)
        end if
        !LaborIncome=Hours*Wage*AgeProd(nAge+1-iAge)*(1.0-taxss)-CommCostTemp !Permanent Shock
        LaborIncomePreTax=DZgrid(nAge+1-iAge,iDZ)*Hours*Wage*
     1               AgeProd(nAge+1-iAge)+Pension
        LaborIncome=DZgrid(nAge+1-iAge,iDZ)*Hours*Wage*
     1              AgeProd(nAge+1-iAge)*(1.0-taxss)+
     1              Pension-CommCostTemp !Stationary Shock
!income constraint applies only if agent was not in RC last period
        if(iRenter.eq.3.and.RCinccut(iLOC,iHF).lt.LaborIncomePreTax.and.
     1     (iRClast.eq.1.or.flagRCstay(iHF).eq.0)) then
         if(iAge.le.nRet) then
          V=MinVal
          flagMinVal=1
          !goto 1197
         else
          Hours=RCinccut(iLOC,iHF)/
     1         (DZgrid(nAge+1-iAge,iDZ)*Wage*AgeProd(nAge+1-iAge))
          if(Hours.gt.HoursMin) then
           LaborIncome=DZgrid(nAge+1-iAge,iDZ)*Hours*Wage*
     1               AgeProd(nAge+1-iAge)*(1.0-taxss)+
     1               Pension-CommCostTemp !Stationary Shock
          else
           V=MinVal
           flagMinVal=1
           !goto 1197
          end if
         end if
        end if
        TaxableIncome=r0*NW+ProfitGrid(iAgg)+Hours*
     1     DZgrid(nAge+1-iAge,iDZ)*Wage*AgeProd(nAge+1-iAge)
        HSVtax=TaxableIncome-
     1         lambda0(iHF)*(TaxableIncome**(1.0-tau0(iHF)))
        HSVtaxBase=TaxableIncome-
     1         lambdaBase*(TaxableIncome**(1.0-tauBase))
        if(HSVtax.lt.0.and.HSVtax.lt.HSVtaxBase) then
         HresMinVoucher=(HSVtaxBase-HSVtax)/Rent(iLOC)
        else
         HresMinVoucher=0.0
        end if

        if(iRenter.eq.1.or.iRenter.eq.3.or.
     1     (iLOC.eq.1.and.iRP1.eq.1).or.
     1     (iLOC.eq.2.and.iRP2.eq.1)) nHchoiceTemp=1

       do iHchoice=1,nHchoiceTemp
        if(flagMinVal.eq.1) goto 1197
!We are not allowing Hchoice>0 if iRP=RPgrid(1).
!If the return on housing is constant, then household is indifferent between investing in housing or in bonds when RP=0 (strictly prefers housing if RP>0) and we are assuming that an indifferent agent chooses bonds
!If the return on housing is volatile, and if housing is not an important hedging asset, then when RP=0 household will always prefer the bond to a risky asset with the same expected return. Thus this is an inocuous restriction
!If the return on housing is volatile, and if housing is a good enough hedge, then households might demand investment assets even when RP<=0.
! For this reason, when a model is converged, need to expand RPgrid s.t. RPgrid(1)<0 and check whether some households buy investment property when RP<=0
        if(iRenter.eq.1.or.iRenter.eq.3.or.
     1     (iLOC.eq.1.and.iRP1.eq.1).or.
     1     (iLOC.eq.2.and.iRP2.eq.1)) then
         Hchoice=0.0
        else
         if(iCchoice.le.nCchoice0) then
          Hchoice=HchoiceGrid0(iHchoice)
         else
          if(iCchoice.eq.nCchoice0+1) then
           if(iNW.gt.1) then
            Hchoice=Policy(iState-nAgg,(iChoiceDisc-1)*2+2)
           else
            Hchoice=0.0
           end if
          else
           tempR1=real(iHchoice-1)/real(nHchoiceTemp1(iCchoice)-1)
           Hchoice=HchoiceMin+(HchoiceMax-HchoiceMin)*tempR1
          end if
         end if
        end if

        if(flagUppBound.eq.1.and.Hchoice.ge.HchoiceUppBound) then
         V=MinVal
         goto 1197
        end if

!HouseConst0=(alphaH/(alphaC*Rent(iLOC)))
!HouseConst1=HouseConst0/(1.0-RCrentred(iLOC,iHF))
!HouseConst2=HouseConst0*(1.0-deprH-taxProp(iHF)-deprINV0)/(1.0-deprH-taxProp(iHF)-deprINV0*PH(iLOC)/Rent(iLOC))
        if(iRenter.eq.1.or.iRenter.eq.3) then
         if(iRenter.eq.1) then
          Hres=Cchoice*(HouseConst0**(1.0/(1.0-ElastCH)))
          if(Hres.lt.HresMin) Hres=HresMin !impose min housing size constraint
          if(Hres.lt.HresMinVoucher) Hres=HresMinVoucher
         else
          Hres=Cchoice*(HouseConst1**(1.0/(1.0-ElastCH)))
          if(Hres.lt.HresMin) Hres=HresMin !impose min housing size constraint
          if(Hres.lt.HresMinVoucher) Hres=HresMinVoucher
          tempR1=RChsize(iLOC,iHF)/
     1          (Rent(iLOC)*(1.0-RCrentred(iLOC,iHF)))
          if(Hres.gt.tempR1) then   !impose max RC size constraint
           Hres=tempR1
           if(Hres.lt.HresMin.or.Hres.lt.HresMinVoucher) then !then impose min housing size
            V=MinVal
            goto 1197
           end if
          end if
         end if
        else
         Hres=Cchoice*(HouseConst2**(1.0/(1.0-ElastCH)))
         if(Hres.lt.HresMin) Hres=HresMin !impose min housing size constraint
         if(Hres.lt.HresMinVoucher) Hres=HresMinVoucher
        end if
        if(iLOC.eq.2.and.Cchoice.gt.CluxCut(flagRet)) then
         Hres=Hres*(1.0+CluxCost(flagRet))
         if(Hres.lt.HresMin) Hres=HresMin !impose min housing size constraint
         if(Hres.lt.HresMinVoucher) Hres=HresMinVoucher
         tempR1=RChsize(iLOC,iHF)/(Rent(iLOC)*(1.0-RCrentred(iLOC,iHF)))
         if (iRenter.eq.3.and.Hres.gt.tempR1) then
          Hres=tempR1
          if(Hres.lt.HresMin.or.Hres.lt.HresMinVoucher) then !then impose min housing size
           V=MinVal
           goto 1197
          end if
         end if
        end if
        if(iAge.le.nRet.or.Hours.lt.0.00001) then
         UtilConst0=(1.0-LeisureMin-CommCost(iLOC,2)-Hours)**chi0
        else
         UtilConst0=(1.0-LeisureMin-CommCost(iLOC,1)-Hours)**chi0
        end if
!        Util=(1.0/(1.0-gamma0))*(
!     1        (Cchoice**(alphaC*(1.0-alphaN)))*
!     1        (Hres**(alphaH*(1.0-alphaN)))*
!     1        (UtilConst0**alphaN)
!     1        )**(1.0-gamma0)
        if(abs(ElastCH).gt.0.0001) then
         UtilConst1=(alphaC*(Cchoice**ElastCH)+alphaH*(Hres**ElastCH))**
     1              (1.0/ElastCH)
        else
         UtilConst1=(Cchoice**alphaC)*(Hres**alphaH)
        end if
        if(abs(ElastCN).gt.0.0001) then
         UtilConst2=((1.0-alphaN)*(UtilConst1**ElastCN)+
     1           alphaN*(UtilConst0**ElastCN))**(1.0/ElastCN)
        else
         UtilConst2=(UtilConst1**(1.0-alphaN))*(UtilConst0**alphaN)
        end if
        Util=(1.0/(1.0-gamma0))*(UtilConst2**(1.0-gamma0))
        if(iLOC.eq.1) then
         Util=Util*(Z1shiftAll**(1.0-gamma0))
        end if
        if(iLOC.eq.1.and.Cchoice.gt.Z1shiftCut(flagRet)) then
         Util=Util*(Z1shiftSize(flagRet)**(1.0-gamma0))
        end if
!        Util=Util+UtilPubGood
        Util=Util*UtilPubGood
        if(Util.lt.VmaxCond) then
         V=Util
         goto 1197
        end if
        if(iRenter.eq.1.or.iRenter.eq.3) then
         if(iRenter.eq.1) then
          Bnext=(1.0/PriceBond)*
     1          (NW+LaborIncome+ProfitGrid(iAgg)-HSVtax-
     1           Rent(iLOC)*Hres-Cchoice-CluxCost0)
         else
          Bnext=(1.0/PriceBond)*
     1          (NW+LaborIncome+ProfitGrid(iAgg)-HSVtax-
     1           Rent(iLOC)*(1.0-RCrentred(iLOC,iHF))*Hres-
     1           Cchoice-CluxCost0)
         end if
         if(Bnext.lt.0.0) then
          Util=MinVal*(0.1-Bnext/10.0)
         end if
        else
         Bnext=(1.0/PriceBond)*
     1   (NW+LaborIncome+ProfitGrid(iAgg)-HSVtax-(PH(iLOC)-Rent(iLOC))*
     1    RCavgrent(iLOC,iHF)*Hchoice-PH(iLOC)*Hres-Cchoice-CluxCost0)
         tempR3=NW-PH(iLOC)*RCavgrent(iLOC,iHF)*Hchoice-PH(iLOC)*Hres
         if(tempR3.lt.-PH(iLOC)*(thetaRes*Hres+
     1                 thetaInv*RCavgrent(iLOC,iHF)*Hchoice)) then
          tempR1=PH(iLOC)*(1.0-thetaInv)*RCavgrent(iLOC,iHF)
          tempR2=PH(iLOC)*(1.0-thetaRes)
          Hres=(NW-Hchoice*tempR1)/tempR2
          if(Hres.lt.HresMin*1.001) then
           flagUppBound=1
           HchoiceUppBound=Hchoice
           Hchoice=0.0
           Hres=NW/tempR2
           if(Hres.lt.HresMin) Hres=HresMin
          end if
          Bnext=(1.0/PriceBond)*
     1    (NW+LaborIncome+ProfitGrid(iAgg)-HSVtax-(PH(iLOC)-Rent(iLOC))*
     1     RCavgrent(iLOC,iHF)*Hchoice-
     1     PH(iLOC)*Hres-Cchoice-CluxCost0)
          if(iAge.le.nRet.or.Hours.lt.0.00001) then
           UtilConst0=(1.0-LeisureMin-CommCost(iLOC,2)-Hours)**chi0
          else
           UtilConst0=(1.0-LeisureMin-CommCost(iLOC,1)-Hours)**chi0
          end if
!          Util=(1.0/(1.0-gamma0))*(
!     1          (Cchoice**(alphaC*(1.0-alphaN)))*
!     1           (Hres**(alphaH*(1.0-alphaN)))*
!     1           (UtilConst0**alphaN)
!     1          )**(1.0-gamma0)
          if(abs(ElastCH).gt.0.0001) then
           UtilConst1=(alphaC*(Cchoice**ElastCH)+
     1                 alphaH*(Hres**ElastCH))**(1.0/ElastCH)
          else
           UtilConst1=(Cchoice**alphaC)*(Hres**alphaH)
          end if
          if(abs(ElastCN).gt.0.0001) then
           UtilConst2=((1.0-alphaN)*(UtilConst1**ElastCN)+
     1             alphaN*(UtilConst0**ElastCN))**(1.0/ElastCN)
          else
           UtilConst2=(UtilConst1**(1.0-alphaN))*(UtilConst0**alphaN)
          end if
          Util=(1.0/(1.0-gamma0))*(UtilConst2**(1.0-gamma0))
          if(iLOC.eq.1) then
           Util=Util*(Z1shiftAll**(1.0-gamma0))
          end if
          if(iLOC.eq.1.and.Cchoice.gt.Z1shiftCut(flagRet)) then
           Util=Util*(Z1shiftSize(flagRet)**(1.0-gamma0))
          end if
!          Util=Util+UtilPubGood
          Util=Util*UtilPubGood
          if(Hres.lt.0.0) then
           Util=MinVal*(0.1-Hres/10.0)
           Hres=0.001
          end if
          tempR1=PH(iLOC)*
     1          (thetaRes*Hres+thetaInv*RCavgrent(iLOC,iHF)*Hchoice)
          tempR2=NW-PH(iLOC)*RCavgrent(iLOC,iHF)*Hchoice-PH(iLOC)*Hres
          if(tempR2.lt.-tempR1*1.001) then
           Util=MinVal*(-tempR2-tempR1)/(0.1-tempR2-tempR1)
          end if
         end if
        end if
        if(Util.lt.VmaxCond) then
         V=Util
         goto 1197
        end if

        EVnext=0
        EVnextBeq=0
        do iHFnext=1,nHF
         PHnext(1)=PH1nextGrid(iAgg,iHFnext)
         PHnext(2)=PH2nextGrid(iAgg,iHFnext)

        do iDepr=1,nDepr

         TrProbDepr=DeprProb(iDepr)
         if(TrProbHF(iHF,iHFnext)*TrProbDepr.lt.0.00001) goto 1194
!If permanent shocks then NWnext depends on DZnext and NWnext must be defined later, otherwise define NWnext here
         if(iRenter.ne.2) then
          if(iDepr.eq.1) then
           TrProbDepr=1.0
          else
           goto 1194
          end if
          NWnext=Bnext!/Normalize  !need normalize for permanent shocks only
         else
          NWnext=Bnext+PHnext(iLOC)*
     1          (1.0-deprH(iLOC)*DeprGrid(iDepr)-taxprop(iHF,iLOC))*
     1          (Hres+Hchoice*RCavgrent(iLOC,iHFnext))-
     1           PHnext(iLOC)*deprINV0*Hchoice*RCavgrent(iLOC,iHFnext)!)/Normalize  !need normalize for permanent shocks only
         end if
         if(NWnext.lt.NWmin) then
          EVnext=MinVal
          EVnextBeq=MinVal*param0 !multiplying by param0 here because dividing by it later
          V=MinVal
          goto 1197
         end if
         call findspot(NWgridNext,nNW,NWnext,
     1                 nint(0.5*real(nNW)),iNWnext)
         EVnextBeq=EVnextBeq+TrProbHF(iHF,iHFnext)*TrProbDepr*
     1            ((NWnext*(1.0-DeathExp)+BeqLux(iDZ))**param0)

        do iDZnext=1,nDZ

!If permanent shocks then NWnext depends on DZ and Normalize must be defined here, otherwise Normalize=1
         if(iAge.le.nRet+1) then
          !if(iDZ.ne.2) goto 1195        !Permanent Shock
          if(iDZ.ne.iDZnext) goto 1195   !Stationary Shock
          !Normalize=1.0
          TrProb=TrProbHF(iHF,iHFnext)*TrProbDepr
         else
          !Normalize=DZgrid(nAge+1-iAge,iDZ) !Permanent Shock
          !Normalize=1.0          !Stationary Shock
          TrProb=TrProbDZ(iDZ,iDZnext)*TrProbHF(iHF,iHFnext)*TrProbDepr
         end if

         if(TrProb.lt.0.0001) goto 1195

!If NWgridAll does not depend on (iAge,iDZ) can define NWgridNext here, otherwise must be later in code
!         do iNWnext=1,nNW
!          if(iAge.eq.1) then
!           NWgridNext(iNWnext)=
!     1      NWgridAll((nAge+1-iAge-1)*nDZ+iDZnext,iNWnext)
!          else
!           NWgridNext(iNWnext)=
!     1      NWgridAll((nAge+2-iAge-1)*nDZ+iDZnext,iNWnext) !When  solving 19 year old's (iAge=2) problem, need to use ValFun and NWgrid of 20 year old
!          end if
!         end do

!If permanent shocks then NWnext depends on DZnext and NWnext must be defined here, otherwise define NWnext ealrier
!         if(iRenter.eq.1.or.iRenter.eq.3) then
!          NWnext=Bnext/Normalize
!          NWnextBeqRec=NWnext+BeqGrid(iAgg,iHFnext)
!         else
!          NWnext=(Bnext+PHnext(iLOC)*
!     1            (Hres+Hchoice*RCavgrent(iLOC,iHF))*(1.0-deprH(iLOC)-taxprop)-
!     1            PHnext(iLOC)*deprINV0*Hchoice*RCavgrent(iLOC,iHF))/Normalize
!          NWnextBeqRec=NWnext+BeqGrid(iAgg,iHFnext)
!         end if
!If permanent shocks then NWnext depends on DZnext and iNWnext must be defined here, otherwise define iNWnext ealrier
!         call findspot(NWgridNext,nNW,NWnext,
!     1        nint(0.5*real(nNW)),iNWnext)
         iIndNext=(iRClastNext-1)*nDZ*nNW+(iDZnext-1)*nNW+iNWnext
         iStateNextL=(iIndNext-1)*nAgg+iAgg
         iStateNextH=iStateNextL+nAgg
         call CHFEV(NWgridNext(iNWnext),NWgridNext(iNWnext+1),
     1              ValFunNext(iStateNextL,iHFnext),
     1              ValFunNext(iStateNextH,iHFnext),
     2              dValFunNext(iStateNextL,iHFnext),
     1              dValFunNext(iStateNextH,iHFnext),
     3              1,NWnext,Vnext,extrap,tempI1)
         if(NWnext.ge.NWgridNext(1).and.NWnext.le.NWgridNext(nNW).and.
     1      (Vnext.lt.ValFunNext(iStateNextL,iHFnext).or.
     1       Vnext.gt.ValFunNext(iStateNextH,iHFnext))) then
          tempR1=(NWnext-NWgridNext(iNWnext))/
     1           (NWgridNext(iNWnext+1)-NWgridNext(iNWnext))
          Vnext=ValFunNext(iStateNextL,iHFnext)+tempR1*
     1         (ValFunNext(iStateNextH,iHFnext)-
     1          ValFunNext(iStateNextL,iHFnext))
         end if
         if(NWnext.lt.NWgridNext(1)) then
          tempR1=(NWnext-(-100.0))/(NWgridNext(1)-(-100.0))
          Vnext=MinVal+tempR1*
     1         (ValFunNext(iStateNextL,iHFnext)-MinVal)+
     1         Hchoice*0.0001*MinVal
         end if
         if(NWnext.gt.NWgridNext(nNW)) then
          tempR1=(NWnext-NWgridNext(iNWnext+1))/
     1            (10000.0-NWgridNext(iNWnext+1))
          Vnext=ValFunNext(iStateNextH,iHFnext)+tempR1*
     1         (0.0-ValFunNext(iStateNextH,iHFnext))
         end if

         !EVnext=EVnext+TrProb*(Normalize**param0)*Vnext!need normalize for permanent shocks only
         EVnext=EVnext+TrProb*Vnext
!These Vnext and EVnext already contain the expectation of receiving a bequest, which was included in ValFunNext

 1195    continue

        end do !iDZnext

 1194   continue

        end do !iDepr
        end do !iHFnext

 1196   continue

        V=Util+beta0*BetaRel(iDZ)*
     1   ((1.0-ProbDeath(nAge+1-iAge))*EVnext+
     1    ProbDeath(nAge+1-iAge)*BeqStrength(iDZ)*EVnextBeq/param0)

 1197   continue

!      if(iWage.eq.3.and.iRent1.eq.3.and.iRent2.eq.3.and.
!     1   iRP1.eq.1.and.iRP2.eq.1.and.iH1.eq.2.and.iH2.eq.2.and.
!     1   iHF.eq.1.and.iNW.eq.16.and.iAge.ge.1.and.
!     1   mod(iDZ,3).eq.2) then
!      if(iCchoice.ge.0.and.iLOC.eq.1.and.iRenter.eq.1) then
!        write(6,'(i4,i4,i4,i4,f10.3,f10.3,f8.4,f8.4,f8.4,f18.5,f18.5,
!     1   f18.5,f18.5,f18.5,f18.5,f18.5,f18.5)')
!     1   iCchoice,iHchoice,iRenter,iLOC,Cchoice,Hchoice,Hres,
!     1   1.0-LeisureMin-CommCost(iLOC,1)-Hours,Bnext,Util,EVnext,
!     1   Util+beta0*BetaRel(iDZ)*(1.0-ProbDeath(nAge+1-iAge))*EVnext+
!     1        beta0*BetaRel(iDZ)*ProbDeath(nAge+1-iAge)*BeqStrength(iDZ)*
!     1        EVnextBeq/param0,V,VmaxCond,
!     1   BeqProb(nAge-iAge+2),EVnextBeq,
!     1   ProbDeath(nAge+1-iAge)*BeqStrength(iDZ)/param0
!       end if
!       end if


        if(V.gt.VmaxCond) then
         VmaxCond=V
!         if(V.gt.Vmax) then
!          Vmax=V
!          ValFun0(iState,1)=V
!         end if
         Policy(iState,(iChoiceDisc-1)*2+1)=Cchoice
         Policy(iState,(iChoiceDisc-1)*2+2)=Hchoice
         ValFunCond(iState,iChoiceDisc)=V
!For the case of persistent RC, some cases don't need to be solved again because the conditional
!value functions are the same as the agent who didn't have RC before. In particular:
!1)iRClast=1 -> this is the baseline case (no RC last period), needs to be solved
!2)iRClast=2 and (iRenter=1 or iRenter=2) -> RC last period, but no RC this period. Does not need to be solved again because conditional value function is identical to baseline case because agent does not choose RC
!3)iRClast=3 and iRenter=3 and (iRClast=2 and iLOC=2) -> This case has zero probability of happening because agent receives RC in different zone from where he had last period. No need to solve
!4)iRClast=3 and iRenter=3 and (iRClast=3 and iLOC=1) -> This case has zero probability of happening because agent receives RC in different zone from where he had last period. No need to solve
!5)iRClast=3 and iRenter=3 and (iRClast=2 and iLOC=1) -> This has a different solution from the baseline case because agent no longer constrained by income constraint
!6)iRClast=3 and iRenter=3 and (iRClast=3 and iLOC=2) -> This has a different solution from the baseline case because agent no longer constrained by income constraint
!Code below fills in all ValFunCond and Policy for iRClast>1, while iRClast=1
!Then, for the cases that are different from baseline (5 and 6) they are redone again by the code above
         if(nRClast.gt.1.and.iRClast.eq.1) then
          do i=2,nRClast
           tempI1=(i-1)*nDZ*nNW+(iDZ-1)*nNW+iNW
           tempI2=(tempI1-1)*nAgg+iAgg
           Policy(tempI2,(iChoiceDisc-1)*2+1)=Cchoice
           Policy(tempI2,(iChoiceDisc-1)*2+2)=Hchoice
           ValFunCond(tempI2,iChoiceDisc)=V
          end do
         end if
         !the piece below updates variables to do a finer search
         tempR1=Cint!CchoiceGrid0(2)-CchoiceGrid0(1)
         tempR2=HchoiceGrid0(2)-HchoiceGrid0(1)
         if(iCchoice.le.nCchoice0+1) then
          CchoiceMin0=Cchoice-2.0*tempR1
          CchoiceMin1=Cchoice-0.5*tempR1
          CchoiceMin2=Cchoice-0.1*tempR1
          if(CchoiceMin0.lt.0.001) CchoiceMin0=0.001
          if(CchoiceMin1.lt.0.001) CchoiceMin1=0.001
          if(CchoiceMin2.lt.0.001) CchoiceMin2=0.001
          CchoiceMax0=Cchoice+2.0*tempR1
          CchoiceMax1=Cchoice+0.5*tempR1
          CchoiceMax2=Cchoice+0.1*tempR1
          if(Cchoice.ge.CchoiceGrid0(nCchoice0)) then
           CchoiceMax0=Cchoice+2.5*tempR1
           CchoiceMax1=Cchoice+1.0*tempR1
           CchoiceMax2=Cchoice+0.5*tempR1
          end if
          HchoiceMin0=Hchoice-2.0*tempR2
          HchoiceMin1=Hchoice-0.5*tempR2
          HchoiceMin1=Hchoice-0.1*tempR2
          if(HchoiceMin0.lt.0.0) HchoiceMin0=0.0
          if(HchoiceMin1.lt.0.0) HchoiceMin1=0.0
          if(HchoiceMin2.lt.0.0) HchoiceMin2=0.0
          HchoiceMax0=Hchoice+2.0*tempR2
          HchoiceMax1=Hchoice+0.5*tempR2
          HchoiceMax2=Hchoice+0.1*tempR2
          if(Hchoice.ge.HchoiceGrid0(nHchoice0)) then
           HchoiceMax0=Hchoice+2.5*tempR2
           HchoiceMax1=Hchoice+1.0*tempR2
           HchoiceMax2=Hchoice+0.5*tempR2
          end if
         end if

         if(iCchoice.gt.nCchoice0+1.and.iCchoice.le.
     1      nCchoice0+1+nCchoice1) then
          CchoiceMin1=Cchoice-0.5*tempR1
          CchoiceMin2=Cchoice-0.1*tempR1
          if(CchoiceMin1.lt.0.001) CchoiceMin1=0.001
          if(CchoiceMin2.lt.0.001) CchoiceMin2=0.001
          CchoiceMax1=Cchoice+0.5*tempR1
          CchoiceMax2=Cchoice+0.1*tempR1
          if(Cchoice.ge.CchoiceMax0-0.01) then
           CchoiceMax1=Cchoice+2.5*tempR1
           CchoiceMax2=Cchoice+1.0*tempR1
          end if
          HchoiceMin1=Hchoice-0.5*tempR2
          HchoiceMin2=Hchoice-0.1*tempR2
          if(HchoiceMin1.lt.0.0) HchoiceMin1=0.0
          if(HchoiceMin2.lt.0.0) HchoiceMin2=0.0
          HchoiceMax1=Hchoice+0.5*tempR2
          HchoiceMax2=Hchoice+0.1*tempR2
          if(Hchoice.ge.HchoiceMax0-0.01) then
           HchoiceMax1=Hchoice+2.5*tempR2
           HchoiceMax2=Hchoice+1.0*tempR2
          end if
         end if

         if(iCchoice.gt.nCchoice0+1+nCchoice1.and.iCchoice.le.
     1      nCchoice0+1+nCchoice1+nCchoice2) then
          CchoiceMin2=Cchoice-0.1*tempR1
          if(CchoiceMin2.lt.0.001) CchoiceMin2=0.001
          CchoiceMax2=Cchoice+0.1*tempR1
          if(Cchoice.ge.CchoiceMax1-0.01) then
           CchoiceMax2=Cchoice+2.5*tempR1
          end if
          HchoiceMin2=Hchoice-0.1*tempR2
          if(HchoiceMin2.lt.0.0) HchoiceMin2=0.0
          HchoiceMax2=Hchoice+0.1*tempR2
          if(Hchoice.ge.HchoiceMax1-0.01) then
           HchoiceMax2=Hchoice+2.5*tempR2
          end if
         end if
        end if

       end do !iHchoice
       end do !iCchoice


 9869  continue

       end do !iLOC
       end do !iRenter

 9871  continue

!This piece of code determines which of the discrete choices is best:
!Before the choice is made, the agent finds out if he won the lottery to live in a rent controlled unit. If he did, he may choose to live in it

!Conditional on not winning the rent controlled lottery, choose best discrete option: rent in z1, rent in z2, own in z1, own in z2
       V=MinVal*10.0
       do iLOC=1,nLOC
       do iRenter=1,2
        iChoiceDisc=(iRenter-1)*nLOC+iLOC
        if(ValFunCond(iState,iChoiceDisc).gt.V) then
         V=ValFunCond(iState,iChoiceDisc)
         ValFunCond(iState,(2+nRC)*nLOC+1)=V
         tempI1=iChoiceDisc
        end if
       end do
       end do
!Next, check if best discrete option is better than rent control.
! -If so, the value function is equal to the best discrete option
! -If not, the value function is equal to the probability weighted average of winning the rent control lottery, or not winning and then choosing the best discrete option
       tempR1=ValFunCond(iState,(3-1)*nLOC+1) !utility of rent controlled in zone1
       tempR2=ValFunCond(iState,(3-1)*nLOC+2) !utility of rent controlled in zone2
       if(V.ge.tempR1.and.V.ge.tempR2) then
        ValFun0(iState,1)=V
       else
!To solve model w/out persistent RC, either set nRClast=1 or keep nRClast=3 and set RCprobTemp=RCprob in all cases
        if(iRClast.eq.1.or.flagRCstay(iHF).eq.0) then
         RCprobTemp(1)=RCprob(iAgg,1)
         RCprobTemp(2)=RCprob(iAgg,2)
        else
         if(iRClast.eq.2) then
          RCprobTemp(1)=RCprobStay(1)
          RCprobTemp(2)=0.0
          if(RCprobStay(1).lt.RCprob(iAgg,1))
     1     RCprobTemp(1)=RCprob(iAgg,1)
         else
          RCprobTemp(1)=0.0
          RCprobTemp(2)=RCprobStay(2)
          if(RCprobStay(2).lt.RCprob(iAgg,2))
     1     RCprobTemp(2)=RCprob(iAgg,2)
         end if
        end if

        if(V.lt.tempR1.and.V.lt.tempR2) then
         ValFun0(iState,1)=V*(1.0-RCprobTemp(1)-RCprobTemp(2))+
     1                     tempR1*RCprobTemp(1)+tempR2*RCprobTemp(2)
        else
         if(V.lt.tempR2) then
          ValFun0(iState,1)=V*(1.0-RCprobTemp(2))+tempR2*RCprobTemp(2)
         else
          ValFun0(iState,1)=V*(1.0-RCprobTemp(1))+tempR1*RCprobTemp(1)
         end if
        end if
       end if
       ValFunCond(iState,(2+nRC)*nLOC+1)=ValFun0(iState,1)


      if(iWage.eq.3.and.iRent1.eq.3.and.iRent2.eq.3.and.
     1   iRP1.eq.1.and.iRP2.eq.1.and.iH1.eq.2.and.iH2.eq.2.and.
     1   iHF.eq.1.and.mod(iNW,4).eq.0.and.iAge.ge.1.and.
     1   mod(iDZ,3).eq.2) then
!      if(iWage.eq.3.and.
!     1   ((iRent1.eq.3.and.iRent2.eq.3.and.iHF.eq.1).or.
!     1    (iRent1.eq.3.and.iRent2.eq.3.and.iHF.eq.1)).and.
!     1   iRP1.eq.1.and.iRP2.eq.1.and.iH1.eq.2.and.iH2.eq.2.and.
!     1   mod(iNW,4).eq.0.and.
!     1   iAge.ge.1.and.iDZ.eq.2) then
!      if(iWage.eq.3.and.iRent1.eq.4.and.iRent2.eq.4.and.
!     1   iRP1.eq.1.and.iRP2.eq.1.and.iH1.eq.2.and.iH2.eq.2.and.
!     1   iHF.eq.1.and.iNW.ge.1.and.iAge.ge.1.and.iDZ.eq.2) then
       !iChoiceDisc=(iRenter-1)*nLOC+iLOC
       iChoiceDisc=tempI1
       iLOC=mod(iChoiceDisc-1,nLOC)+1
       iRenter=((iChoiceDisc-iLOC)/nLOC)+1
       Cchoice=Policy(iState,(iChoiceDisc-1)*2+1)
       Hchoice=Policy(iState,(iChoiceDisc-1)*2+2)
       HouseConst0=(alphaH/(alphaC*Rent(iLOC)))
       HouseConst1=HouseConst0/(1.0-RCrentred(iLOC,iHF))
       HouseConst2=HouseConst0*
     1        (1.0-deprH(iLOC)-taxProp(iHF,iLOC)-deprINV0)/
     1        (1.0-deprH(iLOC)-taxProp(iHF,iLOC)-
     1         deprINV0*PH(iLOC)/Rent(iLOC))
       if(abs(ElastCH).gt.0.0001) then
        HoursConst1=(alphaC+alphaH*
     1  ((alphaH/(alphaC*Rent(iLOC)))**(elastCH/(1.0-elastCH))))**
     1  ((ElastCH-ElastCN)/(ElastCH*(1.0-chi0*ElastCN)))
       else
        HoursConst1=(alphaC*Rent(iLOC)/alphaH)**
     1              (alphaH*ElastCN/(1.0-chi0*ElastCN))
       end if
       Hours=1.0-LeisureMin-CommCost(iLOC,flagRet)-
     1       (Cchoice**param2)*param1*HoursConst0*HoursConst1
       if(iLOC.eq.2.and.Cchoice.gt.CluxCut(flagRet)) then
        Hours=1.0-LeisureMin-CommCost(iLOC,flagRet)-
     1        (Cchoice**param2)*param1*HoursConst0*HoursConst1*
     1       (1.0+CluxCost(flagRet))
       end if
       if(iRenter.eq.1) then
        Hres=Cchoice*(HouseConst0**(1.0/(1.0-ElastCH)))
       else
        Hres=Cchoice*(HouseConst2**(1.0/(1.0-ElastCH)))
       end if
       CluxCost0=0.0
      !if(Hours.lt.0.0) Hours=0.0
       write(6,'(i4,i6,i4,i4,i4,i4,i4,i4,i4,i4,i4,f8.4,i4,i4,
     1  f10.4,f10.4,f10.4,f12.4,f12.4,
     1  f15.5,f15.5,f15.5,f15.5,f15.5,f15.5,f15.5)')
     1 iAge,iAgg,iWage,iRent1,iRent2,iRP1,iRP2,iH1,iH2,
     1 iRClast,iNW,NWgrid(iNW),
     1 iRenter,iLOC,Hchoice,Cchoice,Hres,Hours,
     1 (1.0/PriceBond)*(NW+Hours*Wage-Rent(iLOC)*Hres-Cchoice-
     1  CluxCost0),
     1 (ValFunCond(iState,i),i=1,(2+nRC)*nLOC+1)
!       write(6,*) 21-iAge,iDZ,iNW,iAgg,
!     1 (21-iAge-1)*nInd*nAgg+((iDZ-1)*nNW+iNW-1)*nAgg++iAgg
      end if

      end do !iNW
      end do !iDZ
      end do !iRClast
      end do !iAgg

c$omp end do
c$omp end parallel

      do iState=1,nAgg*nInd
       ValFun(iState,1)=ValFun0(iState,1)
      end do

!      call getfilename(filename,nAge-iAge+1,1,0)
!      call writedata9(Policy,filename,nAgg*nInd,2*(2+nRC)*nLOC,
!     1                nAgg*nInd,2*2*nLOC)
!      call getfilename(filename,nAge-iAge+1,2,0)
!      call writedata9(ValFunCond,filename,nAgg*nInd,2*nLOC,
!     1                nAgg*nInd,2*nLOC)

      call getfilenamedat(filename,nAge-iAge+1,1,0)
      call writedatabinary(Policy,filename,nAgg*nInd,2*(2+nRC)*nLOC)
      call getfilenamedat(filename,nAge-iAge+1,2,0)
      call writedatabinary(ValFunCond,filename,nAgg*nInd,(2+nRC)*nLOC+1)

      end do !iAge

      call writedata(PensionGrid,'Pnsion.txt',nAgg,1,nAgg,1)

      end
!--------------------------------------------------------------
      SUBROUTINE simulate(nAgg,nInd,nWage,nRent1,nRent2,nRP1,nRP2,nH1,
     1     nH2,nNW,nHF,nLOC,nRC,nDZ,nRClast,nAge,nRet,nDepr,nBeqDist,
     1     PriceBond,thetaRes,thetaInv,
     1     deprH,deprINV0,beta0,gamma0,alphaC,alphaH,alphaN,
     1     ElastCH,ElastCN,lambda0,tau0,lambdaBase,tauBase,
     1     chi0,HoursMin,CluxCut,CluxCost,
     1     CommCost,CommCostFin,LeisureMin,taxss,taxprop,taxpropOOT,
     1     DeathExp,
     1     HresMin,RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,
     1     ProfitRedist,RCinccut,RChsize,RCrentred,RCshare,RCprobStay,
     1     flagWelf,nAgent,nFirmC,nFirm1,nFirm2,nAgent0,NWmin,NWmax,
     1     TotYears,NumDeadR,NumDeadW,nRegr,output,outputWelf,outputErr,
     1     TrProbDZuncond,UncondDistDZ,DeprGrid,DeprProb,fracBeq,RCsubs,
     1     flagRCstay,kappa2,kappa3,BetaRel,Z1shiftCut,Z1shiftAll,
     1     Z1shiftSize)
      USE IFPORT
      implicit none
      character(len=9) filename
      integer nAgg,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nLOC
      integer nDZ,nRC,nAge,nRet,nAgent,nAgent0,iHF,iHFnext,iAgg,iState
      integer TotYears,iHFalt,flagWelf,nRegr,iDZ,flagConstZ,nDepr
      !parameter(TotYears=2000)
      integer i,j,t,iNW,nInd,mytime(3),nBeqDist,nRClast,iRClast
      integer tempI1,tempI2,tempI3,tempI4,tempI5,tempI6,tempI7,tempI8
      integer flagRetInd(nAgent),iClMkt,iClMktAlt,flagRCstay(nHF)
      real RCshock(nAgent),RCshock0(nAgent)
      real RCshock1(nAgent),RCshock2(nAgent)
      integer RCreceiver(nAgent),iDepr(nAgent),newborn
      real nFirmC,nFirm1,nFirm2,NWmin,NWmax,fracBeq,DeathExp
      real RCinccut(nLOC,nHF),RChsize(nLOC,nHF)
      real RCrentred(nLOC,nHF),RCprob(nLOC),Hdem(nLOC)
      real RCshare(nLOC,nHF),RCavgrent(nLOC,nHF),RCprobStay(nLOC)
      real NumDeadR,NumDeadW,NumDead,NumRetired,NumDeadExp,CluxCost0
      real BeqShock(nAgent),BeqShock0(nAgent),BeqProb(nAge)
      real PolicyTemp(nAgg*nInd,2*(2+nRC)*nLOC)
      real Policy(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real dPolicyNW(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real dValFunNW(nAge*nAgg*nInd,(2+nRC)*nLOC+1)
      real PolicyTempNW(nNW),dPolicyTempNW(nNW)
      real ValFunCondTemp(nAgg*nInd,(2+nRC)*nLOC+1)
      real ValFunCond(nAge*nAgg*nInd,(2+nRC)*nLOC+1),PensionGrid(nAgg)
      real WageGrid(nWage),Rent1Grid(nRent1),Rent2Grid(nRent2)
      real NWgrid(nNW),NWgridAll(nAge*nDZ,nNW)
      real RP1grid(nRP1),RP2grid(nRP2),DZgrid(nAge,nDZ)
      real H1grid(nH1),H2grid(nH2),HFVgrid(nHF,nLOC)
      real HFgrid0(nHF,nLOC),HFgrid1(nHF,nLOC)
      real TrProbHF(nHF,nHF),TrProbDZ(nDZ,nDZ),AgeProd(nAge)
      real TrProbHFcum(nHF,nHF),TrProbDZcum(nDZ,nDZ),SSIdist(nDZ)
      real Wage,Rent1,Rent2,RP1,RP2,H1last,H2last,H1,H2
      real CluxCut(2),CluxCost(2)
      real WageAlt,Rent1Alt,Rent2Alt,RP1alt,RP2alt
      real NWind(nAgent),Zind(nAgent),Cind(nAgent),Hind(nAgent)
      real LaborIncomeInd(nAgent),HoursInd(nAgent),HresInd(nAgent)
      real ZindNext(nAgent),BnextInd(nAgent)
      real TieBreaker(nAgent,(2+nRC)*nLOC)
      real HindLast(nAgent),HresIndLast(nAgent),Bind(nAgent)
      real ValFunInd(nAgent),ValFunIndAlt(nAgent)
      integer DeathShockIndex(nAgent),LOCind(nAgent),LOCindLast(nAgent)
      integer RenterIndLast(nAgent),RenterInd(nAgent)
      integer RClastInd(nAgent)
      integer AgeIndLast(nAgent),AgeInd(nAgent),AgeIndNext(nAgent)
      integer iZind(nAgent),iZindNext(nAgent),BeqReceiver(nAgent)
      integer iZindLast(nAgent),nDZtemp
      real PriceBond,thetaRes,thetaInv,beta0,gamma0,alphaN,alphaC,alphaH
      real ElastCH,ElastCN,chi0,HoursMin,lambda0(nHF),tau0(nHF)
      real lambdaBase,tauBase
      real deprH(nLOC),deprINV0,taxss,taxprop(nHF,nLOC),CommCost(nLOC,2)
      real LeisureMin,taxpropOOT(nLOC)
      real RTSC,RTSH0loc1,HBARloc1(nHF),RTSH0loc2,HBARloc2(nHF)
      real PensionBelief,Pension,PensionTax,HoursDemand,HresMin
      real HoursDemandC,HoursDemandLOC1,HoursDemandLOC2
      real ProfitC,ProfitLOC1,ProfitLOC2,Profit,ProfitRedist(3)
      real HObeq(nLOC),HIbeq(nLOC),Bbeq,Bequest,CommCostFin(nLOC,2)
      real HObeqExp(nLOC),HIbeqExp(nLOC),BbeqExp,BequestExp
      real Rent(nLOC),PH(nLOC),PHavg(nLOC),Hinv(nLOC)
      real Hours,Cons,DeprGrid(nDepr),DeprProb(nDepr),DeprProbCum(nDepr)
      real HresRenter(nLOC),HresOwner(nLOC),HresRC(nLOC),Hres(nLOC)
      real PH1grid(nAgg,1),PH2grid(nAgg,1),ProbDeath(nAge)
      real tempR1,tempR2,tempR3,tempR4,tempR5,tempR6,tempR7,tempR8
      real tempR9,tempR10,tempR11,tempR12,tempR13,tempR14,tempR15
      real output(TotYears,50),outputBeq(TotYears,nBeqDist*2)
      real outputErr(TotYears,7)
      real outputWelf(TotYears*nAgent0,15),DeathCutoff(nAge,nDZ)
      real DeathShock(nAgent)
      real DeathShockRbeq(nAgent),DeathShockWbeq(nAgent)
      real DeathShockRnbeq(nAgent),DeathShockWnbeq(nAgent)
      real TrProbDZuncond(nDZ,nDZ),TrProbDZuncondCum(nDZ,nDZ) !TrProbDZuncond is the unconditional transition prob
      real uncondDistDZ(1,nDZ),uncondDistDZ0(1,nDZ)           !uncondDistDZ is the unconditional distribution, uncondDistDZ0 contains the cutoffs by number of agents
      integer iRegression,iHFindex,iHFlast
      real RegRHS(12),NWbound(nDZ*nAge,2),NWboundOld(nDZ*nAge,2)
      real Regcoefs1(nRegr,nHF*nHF),Regcoefs2(nRegr,nHF*nHF)
      real Regcoefs3(nRegr,nHF*nHF),Regcoefs4(nRegr,nHF*nHF)
      real Regcoefs5(nRegr,nHF*nHF),Regcoefs6(nRegr,nHF*nHF)
      real Regcoefs7(nRegr,nHF*nHF),Regcoefs0(nRegr,nHF*nHF)
      real Regcoefs8(nRegr,nHF*nHF),Regcoefs9(nRegr,nHF*nHF)
      real Regcoefs10(nRegr,nHF*nHF),Regcoefs11(nRegr,nHF*nHF)
      real BeqInd(nAgent,7),ForDemTot(nLOC)
      real BeqNtile1(nBeqDist),BeqNtile2(nBeqDist),PropTaxIncome
      integer BeqMatch(nAgent)
      real TaxableIncome,TaxableIncomeAvg,HSVtax,r0,kappa2,kappa3
      real HSVgovSurplus,HSVfracPay,HSVmargRate,BetaRel(nDZ)
      real RCsubs(nLOC,nHF),RCavgRentDev(nLOC,nHF)
      real Z1shiftSize(2),Z1shiftCut(2),Z1shiftAll

      r0=1.0-PriceBond
      !flagWelf=1 !Set to 1 if want to compute alternative scenario at each point in time

      nDZtemp=nDZ/2
      if(fracBeq.lt.0.00001) nDZtemp=nDZ

      do i=1,nDZ*nAge
       NWbound(i,1)=100000.0
       NWbound(i,2)=-100000.0
      end do

      do iHF=1,nHF
      do i=1,nLOC
       RCavgrent(i,iHF)=1.0-RCshare(i,iHF)+
     1  RCshare(i,iHF)*(1.0-RCrentred(i,iHF)) !True rent received and price paid relative to market, once accounting for being forced to buy RCshare rent controlled units
       RCavgrentDev(i,iHF)=1.0-RCshare(i,iHF)+
     1  RCshare(i,iHF)*(1.0-RCrentred(i,iHF))*(1.0+RCsubs(i,iHF))
      end do
      end do

      do i=1,TotYears*nAgent0
      do j=1,15
       outputWelf(i,j)=0
      end do
      end do

      do t=1,TotYears
      do i=1,50
       output(t,i)=0.0
       if(i.le.7) outputErr(t,i)=0.0
      end do
      end do

      do i=1,nAgent
       ValFunInd(i)=-99999999
       ValFunIndAlt(i)=-99999999
      end do

      call readdata(NWboundOld,'NWbnd0.txt',nDZ*nAge,2,nDZ*nAge,2)
      call readdata(ProbDeath,'prbdth.txt',nAge,1,nAge,1)
      call readdata(BeqProb,'BeqPrb.txt',nAge,1,nAge,1)
      call readdata(WageGrid,'WGgrid.txt',nWage,1,nWage,1)
      call readdata(Rent1Grid,'R1grid.txt',nRent1,1,nRent1,1)
      call readdata(Rent2Grid,'R2grid.txt',nRent2,1,nRent2,1)
      call readdata(RP1Grid,'P1grid.txt',nRP1,1,nRP1,1)
      call readdata(RP2Grid,'P2grid.txt',nRP2,1,nRP2,1)
      call readdata(H1Grid,'H1grid.txt',nH1,1,nH1,1)
      call readdata(H2Grid,'H2grid.txt',nH2,1,nH2,1)
      call readdata(NWgridAll,'NWgrid.txt',nAge*nDZ,nNW,nAge*nDZ,nNW)
      call readdata(HFgrid0,'HFgri0.txt',nHF,nLOC,nHF,nLOC)
      call readdata(HFgrid1,'HFgri1.txt',nHF,nLOC,nHF,nLOC)
      call readdata(HFVgrid,'FVgrid.txt',nHF,nLOC,nHF,nLOC)
      call readdata(DZgrid,'DZgrid.txt',nAge,nDZ,nAge,nDZ)
      call readdata(SSIdist,'SSdist.txt',nDZ,1,nDZ,1)
      call readdata(TrProbDZ,'ProbDZ.txt',nDZ,nDZ,nDZ,nDZ)
      call readdata(TrProbHF,'ProbHF.txt',nHF,nHF,nHF,nHF)
      call readdata(PensionGrid,'Pnsion.txt',nAgg,1,nAgg,1)
      call readdata(AgeProd,'AgePrd.txt',nAge,1,nAge,1)
      call readdata(PH1grid,'Price1.txt',nAgg,1,nAgg,1)
      call readdata(PH2grid,'Price2.txt',nAgg,1,nAgg,1)
      call readdata(Regcoefs0,'Coef00.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs1,'Coef01.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs2,'Coef02.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs3,'Coef03.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs4,'Coef04.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs5,'Coef05.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs6,'Coef06.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs7,'Coef07.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs8,'Coef08.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs9,'Coef09.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs10,'Coef10.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(Regcoefs11,'Coef11.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)

      DeprProbCum(1)=DeprProb(1)
      if(nDepr.gt.1) then
       do i=2,nDepr
        DeprProbCum(i)=DeprProbCum(i-1)+DeprProb(i)
       end do
      end if

      do j=1,nDZ
       TrProbDZcum(j,1)=TrProbDZ(j,1)
       do i=2,nDZ
        TrProbDZcum(j,i)=TrProbDZcum(j,i-1)+TrProbDZ(j,i)
       end do
      end do
      do iHF=1,nHF
       TrProbHFcum(iHF,1)=TrProbHF(iHF,1)
       do iHFnext=2,nHF
        TrProbHFcum(iHF,iHFnext)=TrProbHFcum(iHF,iHFnext-1)+
     1                           TrProbHF(iHF,iHFnext)
       end do
      end do

      do i=1,nAge
!       write(6,*) i
!       call getfilename(filename,i,1,0)
!       call readdata9(PolicyTemp,filename,nAgg*nInd,2*(2+nRC)*nLOC,
!     1                nAgg*nInd,2*2*nLOC)
!       call getfilename(filename,i,2,0)
!       call readdata9(ValFunCondTemp,filename,nAgg*nInd,(2+nRC)*nLOC,
!     1                nAgg*nInd,2*nLOC)
       call getfilenamedat(filename,i,1,0)
       call readdatabinary(PolicyTemp,filename,nAgg*nInd,2*(2+nRC)*nLOC)
       call getfilenamedat(filename,i,2,0)
       call readdatabinary(ValFunCondTemp,filename,nAgg*nInd,
     1                     (2+nRC)*nLOC+1)
       do iState=1,nAgg*nInd
        do tempI1=1,2*(2+nRC)*nLOC
         Policy((i-1)*nAgg*nInd+iState,tempI1)=PolicyTemp(iState,tempI1)
        end do
        do tempI1=1,(2+nRC)*nLOC+1
         ValFunCond((i-1)*nAgg*nInd+iState,tempI1)=
     1       ValFunCondTemp(iState,tempI1)
        end do
       end do

!        do iState=1,nAgg*nInd
!         ValFunCond((i-1)*nAgg*nInd+iState,(nRC+2)*nLOC+1)=
!     1        ValFunCond((i-1)*nAgg*nInd+iState,1)
!        do tempI1=2,(2+nRC)*nLOC
!         if(ValFunCond((i-1)*nAgg*nInd+iState,tempI1).gt.
!     1      ValFunCond((i-1)*nAgg*nInd+iState,(nRC+2)*nLOC+1)) then
!          ValFunCond((i-1)*nAgg*nInd+iState,(nRC+2)*nLOC+1)=
!     1      ValFunCond((i-1)*nAgg*nInd+iState,tempI1)
!         end if
!        end do
!        end do


!Compute derivatives of valfun w/ respect to NW
c$omp parallel
c$omp& default(none)
c$omp& shared(i,iAgg,nInd,nAgg,nLOC,nRC,nNW,nDZ,NWgridAll,Policy,
c$omp& dValFunNW,ValFunCond,nRClast)
c$omp& private(iNW,iDZ,iState,PolicyTempNW,dPolicyTempNW,NWgrid,
c$omp& tempI1,tempI2,tempI3,iRClast)
c$omp do
       do iAgg=1,nAgg
       do iRClast=1,nRClast
       do iDZ=1,nDZ
       do tempI1=1,(2+nRC)*nLOC+1
        do iNW=1,nNW
         NWgrid(iNW)=NWgridAll((i-1)*nDZ+iDZ,iNW)
         iState=((iRClast-1)*nDZ*nNW+(iDZ-1)*nNW+iNW-1)*nAgg+iAgg
         PolicyTempNW(iNW)=ValFunCond((i-1)*nAgg*nInd+iState,tempI1)
        end do
        tempI2=1
        tempI3=0
        call PCHIM(nNW,NWgrid,PolicyTempNW,dPolicyTempNW,tempI2,tempI3)
        do iNW=1,nNW
         iState=((iRClast-1)*nDZ*nNW+(iDZ-1)*nNW+iNW-1)*nAgg+iAgg
         dValFunNW((i-1)*nAgg*nInd+iState,tempI1)=dPolicyTempNW(iNW)
        end do
       end do
       end do
       end do
       end do
c$omp end do
c$omp end parallel


!Compute derivatives of Policy w/ respect to NW
c$omp parallel
c$omp& default(none)
c$omp& shared(i,iAgg,nInd,nAgg,nLOC,nRC,nNW,nDZ,NWgridAll,Policy,
c$omp& dPolicyNW,nRClast)
c$omp& private(tempI1,tempI2,tempI3,iNW,iDZ,iState,PolicyTempNW,
c$omp& dPolicyTempNW,NWgrid,iRClast)
c$omp do
       do iAgg=1,nAgg
       do iRClast=1,nRClast
       do iDZ=1,nDZ
       do tempI1=1,2*(2+nRC)*nLOC
        do iNW=1,nNW
         NWgrid(iNW)=NWgridAll((i-1)*nDZ+iDZ,iNW)
         iState=((iRClast-1)*nNW*nDZ+(iDZ-1)*nNW+iNW-1)*nAgg+iAgg
         PolicyTempNW(iNW)=Policy((i-1)*nAgg*nInd+iState,tempI1)
        end do
        tempI2=1
        tempI3=0
        call PCHIM(nNW,NWgrid,PolicyTempNW,dPolicyTempNW,tempI2,tempI3)
        do iNW=1,nNW
         iState=((iRClast-1)*nNW*nDZ+(iDZ-1)*nNW+iNW-1)*nAgg+iAgg
         dPolicyNW((i-1)*nAgg*nInd+iState,tempI1)=dPolicyTempNW(iNW)
        end do
       end do
       end do
       end do
       end do
c$omp end do
c$omp end parallel


      end do   !i

!        do i=1,nAge*nAgg*nInd
!        ValFunCond(i,(nRC+2)*nLOC+1)=ValFunCond(i,1)
!        do tempI1=2,(2+nRC)*nLOC
!         if(ValFunCond(i,tempI1).gt.ValFunCond(i,(nRC+2)*nLOC+1)) then
!          ValFunCond(i,(nRC+2)*nLOC+1)=ValFunCond(i,tempI1)
!         end if
!        end do
!        end do

!Start off with a realistic age distribution
      call readdata(Cind,'AgeInt.txt',nAgent,1,nAgent,1)
      do i=1,nAgent
       AgeIndNext(i)=real(Cind(i))
       AgeInd(i)=AgeIndNext(i)
      end do

!Compute the unconditional distribution of the idiosyncratic productivity variable
!uncondDistDZ contains the distribution
!uncondDistDZ0 contains the cutoffs on a uniform space w/ nAgents (uncondDistDZ1(1,nDZ)=nAgent)
      do j=1,nDZ
       TrProbDZuncondCum(j,1)=TrProbDZuncond(j,1)
       do i=2,nDZ
        TrProbDZuncondCum(j,i)=TrProbDZuncondCum(j,i-1)+
     1                         TrProbDZuncond(j,i)
       end do
       !write(6,*) (TrProbDZ0cum(j,i),i=1,3)
      end do
      tempR1=uncondDistDZ(1,1)
      uncondDistDZ0(1,1)=tempR1*real(nAgent)
      do i=2,nDZ
       tempR1=tempR1+uncondDistDZ(1,i)
       uncondDistDZ0(1,i)=real(nAgent)*tempR1*1.0001
      end do

      flagConstZ=0
      tempR1=1.0
      do i=1,nDZ
       tempR1=tempR1*TrProbDZuncond(i,i)
      end do
      if(abs(tempR1-1.0).lt..0001) then
       flagConstZ=1
       if(nDZ.eq.3) then
        uncondDistDZ0(1,1)=nint(real(nAgent)*0.25)
        uncondDistDZ0(1,2)=nint(real(nAgent)*0.75)
        uncondDistDZ0(1,3)=nint(real(nAgent)*1.01)+1
       end if
      end if

      if(nDZtemp.ne.nDZ) then
       newborn=nint(NumDeadW*fracBeq)+nint(NumDeadW*(1.0-fracBeq))+
     1         nint(NumDeadR*fracBeq)+nint(NumDeadR*(1.0-fracBeq))
       tempI1=nint(real(newborn)*uncondDistDZ0(1,nDZ)/real(nAgent))-
     1        nint(real(newborn)*uncondDistDZ0(1,nDZtemp)/real(nAgent))   !This is the number of newborn bequester agents
       tempI2=nint(NumDeadR*fracBeq)+nint(NumDeadW*fracBeq)               !This is the number of dead bequester agents. These two may not be the same due to rounding arror
       tempR1=real(tempI1-tempI2)*0.5
       uncondDistDZ0(1,nDZtemp)=uncondDistDZ0(1,nDZtemp)+
     1                          tempR1*real(nAgent)/real(newborn)
      end if

      tempR1=real(nAgent)/real(nAge)
      tempI1=1
      do i=1,nAgent
       !AgeIndNext(i)=mod(i-1,nAge)+1
       !AgeInd(i)=i
       if(i.le.uncondDistDZ0(1,tempI1)) then
        iZindNext(i)=tempI1
       else
        tempI1=tempI1+1
        iZindNext(i)=tempI1
       end if
       iZind(i)=iZindNext(i)
       !ZindNext(i)=1.0                           !Permanent Shock
       ZindNext(i)=DZgrid(AgeIndNext(i),iZindNext(i)) !Stationary Shock
       LOCind(i)=mod(i-1,2)+1
       RenterInd(i)=mod(i-1,2)+1
       if(RenterInd(i).eq.1) then
        BnextInd(i)=0.01!2.0+0.3*(real((i-AgeIndNext(i))/tempR1)-4.5)
        Hind(i)=0.0
        HresInd(i)=0.0*(2.0+0.3*(real((i-AgeIndNext(i))/tempR1)-4.5))
       else
        BnextInd(i)=0.01!1.0*(2.0+0.3*(real((i-AgeIndNext(i))/tempR1)-4.5))
        Hind(i)=0.0*(2.0+0.3*(real((i-AgeIndNext(i))/tempR1)-4.5))
        HresInd(i)=0.0*(2.0+0.3*(real((i-AgeIndNext(i))/tempR1)-4.5))
       end if
       iDepr(i)=mod(i-1,nDepr)+1
      end do

      Wage=1.0*WageGrid(1)
      Rent1=1.0*Rent1grid(2)
      Rent2=1.0*Rent2grid(2)
      RP1=1.0*RP1grid(1)
      RP2=1.0*RP2grid(1)
      H1=H1grid(1)*real(nAgent)
      H2=H2grid(1)*real(nAgent)
      iHFnext=1
      iHF=iHFnext

      tempI1=(1-1)*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1      (2-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1      (2-1)*nRP1*nRP2*nH1*nH2*nHF+
     1      (1-1)*nRP2*nH1*nH2*nHF+
     1      (1-1)*nH1*nH2*nHF+(1-1)*nH2*nHF+(1-1)*nHF+iHF   !iAgg in order to have an initial PH
      PH(1)=PH1grid(tempI1,1)  !need to initialize for the first clearmarkets
      PH(2)=PH2grid(tempI1,1)  !need to initialize for the first clearmarkets

      tempI1=0
      if(tempI1.eq.1) then
      call readdata(Cind,'iZ_104.txt',nAgent,1,nAgent,1)
      call readdata(NWind,'LOC104.txt',nAgent,1,nAgent,1)
      call readdata(BnextInd,'RNT104.txt',nAgent,1,nAgent,1)
      call readdata(Hind,'Age104.txt',nAgent,1,nAgent,1)
      call readdata(HoursInd,'RCL104.txt',nAgent,1,nAgent,1)
      call readdata(HresInd,'AgL104.txt',nAgent,1,nAgent,1)
      do i=1,nAgent
       iZindNext(i)=nint(Cind(i))
       AgeIndNext(i)=nint(Hind(i))
       AgeInd(i)=nint(HresInd(i))
       LOCind(i)=nint(NWind(i))
       RClastInd(i)=nint(HoursInd(i))
       RenterInd(i)=nint(BnextInd(i))
      end do
      call readdata(BnextInd,'B__104.txt',nAgent,1,nAgent,1)
      call readdata(Hind,'HI_104.txt',nAgent,1,nAgent,1)
      call readdata(HresInd,'HO_104.txt',nAgent,1,nAgent,1)
      call readdata(ZindNext,'Z__104.txt',nAgent,1,nAgent,1)
      H1=0
      H2=0
      do i=1,nAgent
       ZindNext(i)=DZgrid(AgeIndNext(i),iZindNext(i))
       if(LOCind(i).eq.1) then
        H1=H1+HresInd(i)
       else
        H2=H2+HresInd(i)
       end if
      end do
      end if

      RCprob(1)=RCshare(1,iHFnext)
      RCprob(2)=RCshare(2,iHFnext)


      do t=1,TotYears

      iHFlast=iHF
      iHF=iHFnext
      H1last=H1
      H2last=H2
      NumRetired=0
      NumDead=0
      NumDeadExp=0
      Bbeq=0
      BbeqExp=0
      do i=1,nLOC
       HObeq(i)=0
       HIbeq(i)=0
       HObeqExp(i)=0
       HIbeqExp(i)=0
      end do

      do i=1,nAgent
       BeqInd(i,1)=0
       BeqInd(i,2)=0
       BeqInd(i,3)=0
       BeqInd(i,4)=0
       BeqInd(i,5)=0
       BeqInd(i,6)=0
       BeqInd(i,7)=0
      end do

      do i=1,nAgent
       AgeIndLast(i)=AgeInd(i)
       AgeInd(i)=AgeIndNext(i)
       flagRetInd(i)=2
       if(AgeInd(i).le.nAge-nRet) flagRetInd(i)=1
       iZindLast(i)=iZind(i)
       iZind(i)=iZindNext(i)
       Zind(i)=DZgrid(AgeInd(i),iZind(i))!ZindNext(i)
       Bind(i)=BnextInd(i)
       HindLast(i)=Hind(i)
       HresIndLast(i)=HresInd(i)
       LOCindLast(i)=LOCind(i)
       RenterIndLast(i)=RenterInd(i)
       if(nRClast.eq.1.or.RenterIndLast(i).ne.3.or.AgeInd(i).eq.1) then
        RClastInd(i)=1
       else
        RClastInd(i)=1+LOCindLast(i)
       end if
       do tempI1=1,2*nLoC
        TieBreaker(i,tempI1)=1.0+0.0002*(rand()-0.5)
       end do
       if(AgeInd(i).gt.nAge-nRet) then
!       if(AgeProd(AgeInd(i)).lt.0.02) then
        Numretired=NumRetired+1
       end if
       NumDeadExp=NumDeadExp+ProbDeath(AgeIndLast(i))
       BbeqExp=BbeqExp+Bind(i)*ProbDeath(AgeIndLast(i))*(1.0-DeathExp)
       if(RenterIndLast(i).eq.2) then
        HObeqExp(LOCindLast(i))=HObeqExp(LOCindLast(i))+
     1            HresIndLast(i)*ProbDeath(AgeIndLast(i))*(1.0-DeathExp)
        HIbeqExp(LOCindLast(i))=HIbeqExp(LOCindLast(i))+
     1            HindLast(i)*ProbDeath(AgeIndLast(i))*(1.0-DeathExp)
       end if
       if(AgeInd(i).eq.1) then
        NumDead=NumDead+1
        Bbeq=Bbeq+Bind(i)*(1.0-DeathExp)
        if(RenterIndLast(i).eq.2) then
         HObeq(LOCindLast(i))=HObeq(LOCindLast(i))+
     1                        HresIndLast(i)*(1.0-DeathExp)
         HIbeq(LOCindLast(i))=HIbeq(LOCindLast(i))+
     1                        HindLast(i)*(1.0-DeathExp)
        end if
        BeqInd(nint(NumDead),1)=Bind(i)*(1.0-DeathExp)
        if(RenterIndLast(i).eq.2) then
         BeqInd(nint(NumDead),1+LOCind(i))=HresIndLast(i)*(1.0-DeathExp)
         BeqInd(nint(NumDead),3+LOCind(i))=HindLast(i)*(1.0-DeathExp)
        end if
        BeqInd(nint(NumDead),6)=real(iZindLast(i))
        BeqInd(nint(NumDead),7)=real(iDepr(i))
       end if
      end do

      do i=1,nLOC
       HObeq(i)=HObeq(i)/real(NumDead)
       HIbeq(i)=HIbeq(i)/real(NumDead)
       HObeqExp(i)=HObeqExp(i)/real(NumDeadExp)
       HIbeqExp(i)=HIbeqExp(i)/real(NumDeadExp)
      end do
      Bbeq=Bbeq/real(NumDead)
      BbeqExp=BbeqExp/real(NumDeadExp)

      if(t.eq.0) then
      call writedata(Bind,'B__104.txt',nAgent,1,nAgent,1)
      call writedata(HindLast,'HI_104.txt',nAgent,1,nAgent,1)
      call writedata(HresIndLast,'HO_104.txt',nAgent,1,nAgent,1)
      call writedata(Zind,'Z__104.txt',nAgent,1,nAgent,1)
      do i=1,nAgent
       Cind(i)=real(iZind(i))
       Hind(i)=real(AgeInd(i))
       HresInd(i)=real(AgeIndLast(i))
       HoursInd(i)=real(RClastInd(i))
       NWind(i)=real(LOCindLast(i))
       BnextInd(i)=real(RenterIndLast(i))
      end do
      call writedata(Cind,'iZ_104.txt',nAgent,1,nAgent,1)
      call writedata(NWind,'LOC104.txt',nAgent,1,nAgent,1)
      call writedata(BnextInd,'RNT104.txt',nAgent,1,nAgent,1)
      call writedata(Hind,'Age104.txt',nAgent,1,nAgent,1)
      call writedata(HoursInd,'RCL104.txt',nAgent,1,nAgent,1)
      call writedata(HresInd,'AgL104.txt',nAgent,1,nAgent,1)
      end if


!Here insert decision of who gets bequest and who does not
!Then set all newborns wealth to zero. Then give all receives the bequest by category --> that way clearmarkets is unchanged
      do i=1,nAgent
       if(BeqProb(AgeInd(i)).lt.0.0001) then
        BeqShock(i)=2.0
       else
        BeqShock(i)=rand()-BeqProb(AgeInd(i))
       end if
       BeqShock0(i)=BeqShock(i)
       if(nRC.gt.0) then
        RCshock(i)=rand()
        RCshock0(i)=100.0+real(i)
        RCshock1(i)=100.0+real(i)
        RCshock2(i)=100.0+real(i)
        if(RClastInd(i).eq.1) then
         RCshock0(i)=RCshock(i)  !ranking for those that were not in RC
        else
         if(RClastInd(i).eq.2) then
          RCshock1(i)=RCshock(i)   !ranking for those that were in RC1
         else
          RCshock2(i)=RCshock(i)   !ranking for those that were in RC2
         end if
        end if
       end if
      end do
      call sort(RCshock0,nAgent,DeathShockIndex)  !ranking for those that were not in RC
      call sort(RCshock1,nAgent,DeathShockIndex)  !ranking for those that were in RC1
      call sort(RCshock2,nAgent,DeathShockIndex)  !ranking for those that were in RC2
      call sort(BeqShock0,nAgent,DeathShockIndex)


      do i=1,nAgent
       if(AgeInd(i).eq.1) then
        Bind(i)=0
        HresIndLast(i)=0
        HindLast(i)=0
        RenterIndLast(i)=1
       end if
       BeqMatch(i)=0
      end do
!Go through all agents, starting with the lowest (relative) BeqShock, and match them w/ bequesters until run out of bequesters
      do i=1,nAgent
       j=DeathShockIndex(i)
       BeqReceiver(j)=0
       do tempI1=1,nint(NumDead)
        if(BeqMatch(tempI1).eq.0) then
        if(fracBeq.lt.0.00001.or.
     1     (nint(BeqInd(tempI1,6)).le.nDZ/2.and.iZind(j).le.nDZ/2).or.
     1     (nint(BeqInd(tempI1,6)).gt.nDZ/2.and.iZind(j).gt.nDZ/2)) then
         BeqMatch(tempI1)=1    !This variable is zero if bequester tempI1 in BeqInd(tempI1) has not been matched to a receiver
         BeqReceiver(j)=tempI1
         goto 2912
        end if
        end if
       end do
 2912  continue
      end do

!      do i=1,nAgent
!       if(AgeInd(i).eq.1) then
!        Bind(i)=0
!        HresIndLast(i)=0
!        HindLast(i)=0
!        RenterIndLast(i)=1
!       end if
!       BeqReceiver(i)=0
!       if(BeqShock(i).le.BeqShock0(nint(NumDead))) BeqReceiver(i)=1
!      end do

      if(t.gt.1) then
       RegRHS(1)=1
       RegRHS(2)=output(t-1,2)
       RegRHS(3)=output(t-1,3)
       RegRHS(4)=output(t-1,4)
       RegRHS(5)=output(t-1,5)
       RegRHS(6)=output(t-1,6)
       RegRHS(7)=output(t-1,7)
       RegRHS(8)=output(t-1,8)
       RegRHS(9)=0.5*(output(t-1,3)+output(t-1,4))
       RegRHS(10)=0.5*(output(t-1,5)+output(t-1,6))
       RegRHS(11)=0.5*(output(t-1,7)+output(t-1,8))
       RegRHS(12)=0.0
      end if

      iClMktAlt=0
      if(flagWelf.eq.1) then
       if(iHF.eq.1) then
        iHFalt=2
       else
        iHFalt=1
       end if
       if(t.le.10000) then
        WageAlt=Wage
        Rent1Alt=Rent1
        Rent2Alt=Rent2
        RP1alt=RP1
        RP2alt=RP2
       else
        iHFindex=(iHFlast-1)*nHF+iHFalt
        do iRegression=1,5
         tempR1=RegCoefs0(iRegression,iHFindex)*RegRHS(1)+
     1          RegCoefs1(iRegression,iHFindex)*RegRHS(2)+
     1          RegCoefs2(iRegression,iHFindex)*RegRHS(3)+
     1          RegCoefs3(iRegression,iHFindex)*RegRHS(4)+
     1          RegCoefs4(iRegression,iHFindex)*RegRHS(5)+
     1          RegCoefs5(iRegression,iHFindex)*RegRHS(6)+
     1          RegCoefs6(iRegression,iHFindex)*RegRHS(7)+
     1          RegCoefs7(iRegression,iHFindex)*RegRHS(8)+
     1          RegCoefs8(iRegression,iHFindex)*RegRHS(9)+
     1          RegCoefs9(iRegression,iHFindex)*RegRHS(10)+
     1          RegCoefs10(iRegression,iHFindex)*RegRHS(11)+
     1          RegCoefs11(iRegression,iHFindex)*RegRHS(12)
         if(iRegression.eq.1) WageAlt=tempR1
         if(iRegression.eq.2) Rent1Alt=tempR1
         if(iRegression.eq.3) Rent2Alt=tempR1
         if(iRegression.eq.4) RP1Alt=tempR1
         if(iRegression.eq.5) RP2Alt=tempR1
        end do

        if(Wagealt.lt.WageGrid(1)) Wagealt=WageGrid(1)
        if(Wagealt.gt.WageGrid(nWage)) Wagealt=WageGrid(nWage)
        if(Rent1alt.lt.Rent1grid(1)) Rent1alt=Rent1grid(1)
        if(Rent1alt.gt.Rent1grid(nRent1)) Rent1alt=Rent1grid(nRent1)
        if(Rent2alt.lt.Rent2grid(1)) Rent2alt=Rent2grid(1)
        if(Rent2alt.gt.Rent2grid(nRent2)) Rent2alt=Rent2grid(nRent2)
        if(RP1alt.lt.RP1grid(1)) RP1alt=RP1grid(1)
        if(RP1alt.gt.RP1grid(nRP1)) RP1alt=RP1grid(nRP1)
        if(RP2alt.lt.RP2grid(1)) RP2alt=RP2grid(1)
        if(RP2alt.gt.RP2grid(nRP2)) RP2alt=RP2grid(nRP2)
       end if


       call clearmarkets(t,nWage,nRent1,nRent2,nAgg,nInd,nNW,nDZ,
     1  nRClast,nRP1,
     1  nRP2,nH1,nH2,nHF,nLOC,nRC,nAge,nAgent,nFirmC,nFirm1,nFirm2,
     1  nRet,NumRetired,nDepr,thetaRes,thetaInv,
     1  RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,deprH,deprINV0,
     1  gamma0,alphaC,alphaH,alphaN,ElastCH,ElastCN,
     1  lambda0,tau0,lambdaBase,tauBase,chi0,
     1  HoursMin,CluxCut,CluxCost,ProfitRedist,PriceBond,
     1  flagRetInd,taxss,taxprop,taxpropOOT,HresMin,RCavgrent,
     1  RCavgrentDev,RCinccut,RChsize,RCrentred,RCprob,RCprobStay,
     1  RCshare,RCshock,RCshock0,RCshock1,RCshock2,
     1  WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1  HFgrid0,HFgrid1,HFVgrid,NWgridAll,AgeProd,CommCost,CommCostFin,
     1  LeisureMin,PH1grid,PH2grid,policy,dPolicyNW,dValFunNW,
     1  ValFunCond,PensionGrid,
     1  iHFlast,iHFalt,WageAlt,Rent1Alt,Rent2Alt,Rent,RP1alt,RP2alt,
     1  H1last,H2last,H1,H2,PH,PHavg,
     1  Hours,HoursDemand,Cons,Hres,HresRenter,HresOwner,HresRC,Hinv,
     1  Pension,BbeqExp,HObeqExp,HIbeqExp,BeqReceiver,BeqInd,RCreceiver,
     1  AgeInd,iZind,Zind,NWind,Bind,Cind,HoursInd,Hind,HresInd,
     1  HresIndLast,HindLast,RenterInd,RenterIndLast,RClastInd,
     1  LOCind,LOCindLast,
     1  LaborIncomeInd,ValFunIndAlt,TieBreaker,SSIdist,NWmin,NWmax,
     1  DeprGrid,iDepr,outputErr,TotYears,iClMktAlt,flagRCstay)
      end if

      if(t.gt.10000) then
       iHFindex=(iHFlast-1)*nHF+iHF
        do iRegression=1,5
         tempR1=RegCoefs0(iRegression,iHFindex)*RegRHS(1)+
     1          RegCoefs1(iRegression,iHFindex)*RegRHS(2)+
     1          RegCoefs2(iRegression,iHFindex)*RegRHS(3)+
     1          RegCoefs3(iRegression,iHFindex)*RegRHS(4)+
     1          RegCoefs4(iRegression,iHFindex)*RegRHS(5)+
     1          RegCoefs5(iRegression,iHFindex)*RegRHS(6)+
     1          RegCoefs6(iRegression,iHFindex)*RegRHS(7)+
     1          RegCoefs7(iRegression,iHFindex)*RegRHS(8)+
     1          RegCoefs8(iRegression,iHFindex)*RegRHS(9)+
     1          RegCoefs9(iRegression,iHFindex)*RegRHS(10)+
     1          RegCoefs10(iRegression,iHFindex)*RegRHS(11)+
     1          RegCoefs11(iRegression,iHFindex)*RegRHS(12)
         if(iRegression.eq.1) Wage=tempR1
         if(iRegression.eq.2) Rent1=tempR1
         if(iRegression.eq.3) Rent2=tempR1
         if(iRegression.eq.4) RP1=tempR1
         if(iRegression.eq.5) RP2=tempR1
        end do
        if(Wage.lt.WageGrid(1)) Wage=WageGrid(1)
        if(Wage.gt.WageGrid(nWage)) Wage=WageGrid(nWage)
        if(Rent1.lt.Rent1grid(1)) Rent1=Rent1grid(1)
        if(Rent1.gt.Rent1grid(nRent1)) Rent1=Rent1grid(nRent1)
        if(Rent2.lt.Rent2grid(1)) Rent2=Rent2grid(1)
        if(Rent2.gt.Rent2grid(nRent2)) Rent2=Rent2grid(nRent2)
        if(RP1.lt.RP1grid(1)) RP1=RP1grid(1)
        if(RP1.gt.RP1grid(nRP1)) RP1=RP1grid(nRP1)
        if(RP2.lt.RP2grid(1)) RP2=RP2grid(1)
        if(RP2.gt.RP2grid(nRP2)) RP2=RP2grid(nRP2)
       end if

!      if(t.eq.1) then
!      Wage=0.99543
!      Rent1=0.11508
!      Rent2=0.11508
!      RP1=0.000211
!      RP2=0.000250
!      end if


      call clearmarkets(t,nWage,nRent1,nRent2,nAgg,nInd,nNW,nDZ,
     1  nRClast,nRP1,
     1  nRP2,nH1,nH2,nHF,nLOC,nRC,nAge,nAgent,nFirmC,nFirm1,nFirm2,
     1  nRet,NumRetired,nDepr,thetaRes,thetaInv,
     1  RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,deprH,deprINV0,
     1  gamma0,alphaC,alphaH,alphaN,ElastCH,ElastCN,
     1  lambda0,tau0,lambdaBase,tauBase,chi0,
     1  HoursMin,CluxCut,CluxCost,ProfitRedist,PriceBond,
     1  flagRetInd,taxss,taxprop,taxpropOOT,HresMin,RCavgrent,
     1  RCavgrentDev,RCinccut,RChsize,RCrentred,RCprob,RCprobStay,
     1  RCshare,RCshock,RCshock0,RCshock1,RCshock2,
     1  WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1  HFgrid0,HFgrid1,HFVgrid,NWgridAll,AgeProd,CommCost,CommCostFin,
     1  LeisureMin,PH1grid,PH2grid,policy,dPolicyNW,dValFunNW,
     1  ValFunCond,PensionGrid,iHFlast,
     1  iHF,Wage,Rent1,Rent2,Rent,RP1,RP2,H1last,H2last,H1,H2,PH,PHavg,
     1  Hours,HoursDemand,Cons,Hres,HresRenter,HresOwner,HresRC,Hinv,
     1  Pension,BbeqExp,HObeqExp,HIbeqExp,BeqReceiver,BeqInd,RCreceiver,
     1  AgeInd,iZind,Zind,NWind,Bind,Cind,HoursInd,Hind,HresInd,
     1  HresIndLast,HindLast,RenterInd,RenterIndLast,RClastInd,
     1  LOCind,LOCindLast,
     1  LaborIncomeInd,ValFunInd,TieBreaker,SSIdist,NWmin,NWmax,
     1  DeprGrid,iDepr,outputErr,TotYears,iClMkt,flagRCstay)

      if(t.gt.100) then
      do i=1,nAgent
       tempI1=(AgeInd(i)-1)*nDZ+iZind(i)
       if(NWind(i).le.NWbound(tempI1,1)) NWbound(tempI1,1)=NWind(i)
       if(NWind(i).ge.NWbound(tempI1,2)) NWbound(tempI1,2)=NWind(i)
      end do
      end if




      ForDemTot(1)=exp(HFgrid0(iHF,1)-
     1                 HFgrid1(iHF,1)*log(PH(1)*(1.0+taxpropOOT(1)))) !Foreign Demand per Domestic Household in Zone 1
      ForDemTot(2)=exp(HFgrid0(iHF,2)-
     1                 HFgrid1(iHF,2)*log(PH(2)*(1.0+taxpropOOT(2)))) !Foreign Demand per Domestic Household in Zone 2
      PropTaxIncome=((taxprop(iHF,1)*H1last*PH(1)+
     1                taxprop(iHF,2)*H2last*PH(2))/real(nAgent))+
     1               taxpropOOT(1)*ForDemTot(1)*PH(1)+
     1               taxpropOOT(2)*ForDemTot(2)*PH(2)   ! property tax income per capita
      Hdem(1)=(Hres(1)/real(nAgent))+ForDemTot(1)*HFVgrid(iHF,1)
      Hdem(2)=(Hres(2)/real(nAgent))+ForDemTot(2)*HFVgrid(iHF,2)
      tempR1=1.0-(Hdem(1)/HBARloc1(iHF))
      tempR2=1.0-(Hdem(2)/HBARloc2(iHF))
      if(tempR1.lt.0.0001) tempR1=0.0001
      if(tempR2.lt.0.0001) tempR2=0.0001
      HoursDemandC=nFirmC*(RTSC/Wage)**(1.0/(1.0-RTSC))
      if(abs(RTSH0loc1-1.0).gt.0.0001) then
       HoursDemandLOC1=nFirm1*
     1           (tempR1*RTSH0loc1*PHavg(1)/Wage)**(1.0/(1.0-RTSH0loc1))
      else
       tempR3=Hdem(1)*real(nAgent)-(1.0-deprH(1))*H1last
       HoursDemandLOC1=(tempR3/tempR1)+
     1                 (PHavg(1)-Wage/tempR1)*real(nAgent)*HBARloc1(iHF)
      end if
      if(abs(RTSH0loc2-1.0).gt.0.0001) then
       HoursDemandLOC2=nFirm2*
     1           (tempR2*RTSH0loc2*PHavg(2)/Wage)**(1.0/(1.0-RTSH0loc2))
      else
       tempR4=Hdem(2)*real(nAgent)-(1.0-deprH(2))*H2last
       HoursDemandLOC2=(tempR4/tempR2)+
     1                 (PHavg(2)-Wage/tempR2)*real(nAgent)*HBARloc2(iHF)
      end if
      if(HoursDemandLOC1.lt.0.0001) HoursDemandLOC1=0.0001
      if(HoursDemandLOC2.lt.0.0001) HoursDemandLOC2=0.0001
      ProfitC=nFirmC*(((HoursDemandC/nFirmC)**RTSC)-
     1                (HoursDemandC/nFirmC)*Wage)
      ProfitLOC1=nFirm1*(
     1           PHavg(1)*tempR1*((HoursDemandLOC1/nFirm1)**RTSH0loc1)-
     1          (HoursDemandLOC1/nFirm1)*Wage)
      ProfitLOC2=nFirm2*(
     1           PHavg(2)*tempR2*((HoursDemandLOC2/nFirm2)**RTSH0loc2)-
     1          (HoursDemandLOC2/nFirm2)*Wage)
      Profit=(ProfitC*ProfitRedist(1)+ProfitLOC1*ProfitRedist(2)+
     1        ProfitLOC2*ProfitRedist(3))/real(nAgent)






c$omp parallel
c$omp& default(none)
c$omp& shared(t,i,nAgent0,outputWelf,ValFunInd,ValFunIndAlt,AgeInd,
c$omp& LOCind,RenterIndLast,Bind,HresInd,HresIndLast,HindLast,Cind,Rent,
c$omp& HoursInd,Zind,RenterInd,Hind,NWind,iZind,RCreceiver)
c$omp& private(tempI1)
c$omp do
      do i=1,nAgent0
       tempI1=(t-1)*nAgent0+i
       if(ValFunInd(i).gt.-99999999.and.ValFunInd(i).lt.0) then
        outputWelf(tempI1,1)=ValFunInd(i)
       else
        outputWelf(tempI1,1)=-99999999
       end if
       if(ValFunIndAlt(i).gt.-99999999) then
        outputWelf(tempI1,2)=ValFunIndAlt(i)
       else
        outputWelf(tempI1,2)=-99999999
       end if
       outputWelf(tempI1,3)=real(AgeInd(i))
       outputWelf(tempI1,4)=real(RenterIndLast(i))
       outputWelf(tempI1,5)=real(LOCind(i))
       outputWelf(tempI1,6)=Bind(i)
       outputWelf(tempI1,7)=Hind(i)!HresIndLast(i)+HindLast(i)
       outputWelf(tempI1,8)=Cind(i)
       outputWelf(tempI1,9)=HresInd(i)!HresInd(i)*Rent(LOCind(i))
       outputWelf(tempI1,10)=HoursInd(i)
       outputWelf(tempI1,11)=Zind(i)+0.0001*real(mod(i-1,11)+1-6)
       outputWelf(tempI1,12)=real(RenterInd(i))
       outputWelf(tempI1,13)=NWind(i)
       outputWelf(tempI1,14)=real(iZind(i))
       outputWelf(tempI1,15)=real(RCreceiver(i))
      end do
c$omp end do
c$omp end parallel

!Compute random numbers for death shock. Sort them to make sure the right number of people die each period
      do i=1,nAgent
       DeathShock(i)=rand()-ProbDeath(AgeInd(i))
       if(ProbDeath(AgeInd(i)).lt.0.0001) DeathShock(i)=1.0
       DeathShockWbeq(i)=10000
       DeathShockWnbeq(i)=10000
       DeathShockRbeq(i)=10000
       DeathShockRnbeq(i)=10000
       if(iZind(i).le.nDZtemp) then
        if(AgeInd(i).gt.nAge-nRet) then
         DeathShockRnbeq(i)=DeathShock(i)
        else
         DeathShockWnbeq(i)=DeathShock(i)
        end if
       else
        if(AgeInd(i).gt.nAge-nRet) then
         DeathShockRbeq(i)=DeathShock(i)
        else
         DeathShockWbeq(i)=DeathShock(i)
        end if
       end if
      end do
      call sort(DeathShockWnbeq,nAgent,DeathShockIndex)
      call sort(DeathShockRnbeq,nAgent,DeathShockIndex)
      call sort(DeathShockWbeq,nAgent,DeathShockIndex)
      call sort(DeathShockRbeq,nAgent,DeathShockIndex)
      do i=1,nAge
       if(i.gt.nAge-nRet) then
        do j=1,nDZ
         if(j.le.nDZtemp) then
          DeathCutoff(i,j)=DeathShockRnbeq(nint(NumDeadR*(1.0-fracBeq)))
         else
          DeathCutoff(i,j)=DeathShockRbeq(nint(NumDeadR*fracBeq))
         end if
        end do
       else
        if(NumDeadW.gt.0.001) then
         do j=1,nDZ
          if(j.le.nDZtemp) then
           DeathCutoff(i,j)=
     1                DeathShockWnbeq(nint(NumDeadW*(1.0-fracBeq)))
          else
           DeathCutoff(i,j)=DeathShockWbeq(nint(NumDeadW*fracBeq))
          end if
         end do
        else
         do j=1,nDZ
          DeathCutoff(i,j)=-2.0
         end do
        end if
       end if
      end do

      newborn=0
      HSVgovSurplus=0
      HSVfracPay=0
      HSVmargRate=0
      TaxableIncomeAvg=0
      do i=1,nAgent
       CluxCost0=0.0
       if(Cind(i).gt.CluxCut(flagRetInd(i)).and.LOCind(i).eq.2) then
        CluxCost0=CluxCost(flagRetInd(i))*
     1           (Cind(i)-CluxCut(flagRetInd(i)))
       end if
       TaxableIncome=r0*NWind(i)+Profit+
     1               HoursInd(i)*Zind(i)*Wage*AgeProd(AgeInd(i))
       TaxableIncomeAvg=TaxableIncomeAvg+TaxableIncome
       HSVtax=TaxableIncome-
     1        lambda0(iHF)*(TaxableIncome**(1.0-tau0(iHF)))
       HSVgovSurplus=HSVgovSurplus+HSVtax
       if(TaxableIncome.gt.0.0001) then
        HSVmargRate=HSVmargRate+TaxableIncome*(1.0-(1.0-tau0(iHF))*
     1              lambda0(iHF)*(TaxableIncome**(-tau0(iHF))))
       end if
       if(HSVtax.lt.0) then
        HSVfracPay=HSVfracPay+1.0
       end if
       if(RenterInd(i).eq.1.or.RenterInd(i).eq.3) then
        if(RenterInd(i).eq.1) then
         BnextInd(i)=(1.0/PriceBond)*
     1    (NWind(i)+LaborIncomeInd(i)+Profit-HSVtax-
     1     Rent(LOCind(i))*HresInd(i)-Cind(i)-CluxCost0)
        else
         BnextInd(i)=(1.0/PriceBond)*(NWind(i)+LaborIncomeInd(i)+
     1     Profit-HSVtax-
     1     Rent(LOCind(i))*(1.0-RCrentred(LOCind(i),iHF))*HresInd(i)-
     1     Cind(i)-CluxCost0)
        end if
       else
        BnextInd(i)=(1.0/PriceBond)*
     1   (NWind(i)+LaborIncomeInd(i)+Profit-HSVtax-
     1    (PH(LOCind(i))-
     1     Rent(LOCind(i)))*Hind(i)*RCavgrent(LOCind(i),iHF)-
     1     PH(LOCind(i))*HresInd(i)-Cind(i)-CluxCost0)
       end if
       !if(DeathShock(i).lt.0) then
       if(DeathShock(i).le.DeathCutoff(AgeInd(i),iZind(i))) then
        newborn=newborn+1
        AgeIndNext(i)=1
        !if(flagConstZ.eq.0) iZind(i)=1 !This is done simply so that in next piece of code, all AgeIndNext=1 agents are bunched together in one batch for determining distribution of iZindNext. Not necessary when Z(t+1)=Z(t) for all i,t
        !ZindNext(i)=1.0 !Permanent
       else
        AgeIndNext(i)=AgeInd(i)+1
       end if
       DeathShockWbeq(i)=rand()        !original zshock
       if(AgeIndNext(i).eq.1) then
        DeathShockRbeq(i)=DeathShockWbeq(i)
       else
        DeathShockRbeq(i)=1000.0
       end if
      end do
      HSVgovSurplus=HSVgovSurplus/real(nAgent)
      HSVfracPay=HSVfracPay/real(nAgent)
      HSVmargRate=HSVmargRate/TaxableIncomeAvg  !income weighted marginal tax rate
      TaxableIncomeAvg=TaxableIncomeAvg/real(nAgent)

      call sort(DeathShockRbeq,nAgent,DeathShockIndex)



!This piece of code renormalizes zshock s.t. everyone of same age and iZ is evenly spread on (0,1)
!Not doing this anymore because w/ bequesters, conditioning on iZ leads to pretty small groups
!c$omp parallel
!c$omp& default(none)
!c$omp& shared(j,nAge,nDZ,nAgent,AgeIndNext,iZind,DeathShockWbeq,BeqShock)
!c$omp& private(tempI1,tempI2,tempI3,i,DeathShockRbeq,DeathShockIndex)
!c$omp do
!      do j=1,nAge
!       do tempI1=1,nDZ
!        tempI2=0
!        tempI3=0
!        do i=1,nAgent
!         DeathShockRbeq(i)=10000
!         if(AgeIndNext(i).eq.j) then
!          tempI3=tempI3+1
!          if(iZind(i).eq.tempI1) then
!           tempI2=tempI2+1
!           DeathShockRbeq(i)=DeathShockWbeq(i)  !contains shock for agents of right Age and iZ, 10000 for everyone else
!          end if
!         end if
!        end do
!        call sort(DeathShockRbeq,nAgent,DeathShockIndex)
!        do i=1,tempI2
!         if(tempI2.eq.1) then
!          BeqShock(DeathShockIndex(i))=0.5
!         else
!!           BeqShock(i)=rand()
!!          BeqShock(DeathShockIndex(i))=(1.0/real(tempI2+1))+
!!     1                                 (real(i-1)/real(tempI2+1))+
!!     1         0.0001*(DeathShockWbeq(DeathShockIndex(i))-0.5)   !zshock rescaled so that everyone of same age and iZ is evenly spread on (0,1)
!          BeqShock(DeathShockIndex(i))=real(i-1)/real(tempI2-1)+
!     1                     0.0001*(DeathShockWbeq(DeathShockIndex(i))-0.5)   !zshock rescaled so that everyone of same age and iZ is evenly spread on (0,1)
!          if(BeqShock(DeathShockIndex(i)).lt.0.00001)
!     1       BeqShock(DeathShockIndex(i))=0.00001
!          if(BeqShock(DeathShockIndex(i)).gt.0.99999)
!     1       BeqShock(DeathShockIndex(i))=0.99999
!         end if
!        end do
!       end do
!      end do
!c$omp end do
!c$omp end parallel

      do i=1,nAgent
       BeqShock(i)=DeathShockWbeq(i)
       tempI2=1
       do tempI1=1,nDZ-1
        if(AgeIndNext(i).ne.1) then
         if(BeqShock(i).gt.TrProbDZcum(iZind(i),tempI1))
     1      tempI2=tempI1+1
        else
         tempR1=real(newborn)*uncondDistDZ0(1,tempI1)/real(nAgent)
         if(BeqShock(i).gt.DeathShockRbeq(nint(tempR1))) tempI2=tempI1+1
!         if(BeqShock(i).gt.uncondDistDZ0(1,tempI1)/real(nAgent))
!     1      tempI2=tempI1+1
        end if
       end do
       if(AgeInd(i).ge.nAge-nRet.and.AgeIndNext(i).ne.1) then
        !ZindNext(i)=Zind(i)    !Permanent Shock
        iZindNext(i)=iZind(i)   !Stationary Shock
       else
        !ZindNext(i)=Zind(i)*DZgrid(AgeIndNext(i),tempI2)     !Permanent Shock
        iZindNext(i)=tempI2                      !Stationary Shock
       end if
       !ZindNext(i)=DZgrid(AgeIndNext(i),iZindNext(i))          !Stationary Shock
      end do !i

!Permanent shock
!Set Avg[Z|Age]=1 so that a small nAgent doesn't add as much idiosyncratic risk
!      do tempI1=1,nAge-nRet
!       tempR1=0
!       tempI2=0
!       do i=1,nAgent
!        if(AgeIndNext(i).eq.tempI1) then
!         tempR1=tempR1+ZindNext(i)
!         tempI2=tempI2+1
!        end if
!       end do
!       tempR1=tempR1/real(tempI2)
!       do i=1,nAgent
!        if(AgeIndNext(i).eq.tempI1) then
!         ZindNext(i)=ZindNext(i)/tempR1
!        end if
!       end do
!      end do
!Stationary shock
!      tempR1=0
!      tempI1=0
!      do i=1,nAgent
!       if(AgeIndNext(i).le.nAge-nRet) then
!        tempR1=tempR1+ZindNext(i)
!        tempI1=tempI1+1
!       end if
!      end do
!      tempR1=tempR1/real(tempI1)
!      do i=1,nAgent
!       ZindNext(i)=ZindNext(i)/tempR1
!      end do

      if(nDepr.gt.1) then
       do i=1,nAgent
        tempR1=rand()
        tempI1=1
        do tempI2=1,nDepr-1
         if(tempR1.gt.DeprProbCum(tempI2)) tempI1=tempI2+1
        end do
        iDepr(i)=tempI1
       end do
      else
       do i=1,nAgent
        iDepr(i)=1
       end do
      end if

      tempR1=rand()
      iHFnext=1
      do tempI1=1,nHF-1
       if(tempR1.gt.TrProbHFcum(iHF,tempI1)) iHFnext=iHFnext+1
      end do

      if(abs(TrProbHF(1,1)-1.0).lt.0.00001.and.
     1   abs(TrProbHF(2,2)-1.0).lt.0.00001) then
!       if(t.eq.nint(real(TotYears)*0.333)) iHFnext=2
!       if(t.eq.nint(real(TotYears)*0.667)) iHFnext=1
       if(mod(t,100).eq.0) then
        if(iHF.eq.1) iHFnext=2
        if(iHF.eq.2) iHFnext=1
       end if
      end if

      Bequest=Bbeq
      BequestExp=BbeqExp
      do i=1,nLOC
       Bequest=Bequest+PH(i)*
     1  (HObeq(i)*(1.0-deprH(i)-taxprop(iHF,i))+
     1   HIbeq(i)*(1.0-deprH(i)-taxprop(iHF,i)-
     1   deprINV0)*RCavgrent(i,iHF))
       BequestExp=BequestExp+PH(i)*
     1  (HObeqExp(i)*(1.0-deprH(i)-taxprop(iHF,i))+
     1   HIbeqExp(i)*(1.0-deprH(i)-taxprop(iHF,i)-
     1   deprINV0)*RCavgrent(i,iHF))
      end do

      call BeqDistMoments(nAgent,nDZ,nDepr,nBeqDist,NumDead,
     1          BeqInd,PH,taxprop,deprH,deprINV0,DeprGrid,fracBeq,
     1          BeqNtile1,BeqNtile2,RCavgrent,nLOC,nHF,iHF,t)
!       write(6,'(i5,f9.4,f9.4,f9.4,f9.4,f9.4,f9.4,f9.4,f9.4)')
!     1 t,Bequest,BequestExp,(BeqNtile1(i),i=1,nBeqDist),
!     1 (BeqNtile2(i),i=1,nBeqDist)
      do i=1,nBeqDist
       outputBeq(t,i)=BeqNtile1(i)
       outputBeq(t,nBeqDist+i)=BeqNtile2(i)
      end do

!      tempR1=0
!      do i=1,nAgent
!       tempR1=tempR1+NWind(i)/real(nAgent)
!      end do
!      write(6,'(i5,f8.4,f8.4,f8.4,f8.4,f8.4)')
!     1 t,tempR1,(outputBeq(t,i),i=1,nBeqDist+1)

      output(t,1)=real(iHF)
      output(t,2)=Wage
      output(t,3)=Rent(1)
      output(t,4)=Rent(2)
      output(t,5)=RP1
      output(t,6)=RP2
      output(t,7)=H1last/real(nAgent)!H1/real(nAgent)
      output(t,8)=H2last/real(nAgent)!H2/real(nAgent)
      output(t,9)=BequestExp
      output(t,10)=PH(1)
      output(t,11)=PH(2)
      output(t,12)=HoursDemand
      output(t,13)=Hours
      output(t,14)=Hres(1)/real(nAgent)
      output(t,15)=Hres(2)/real(nAgent)
      output(t,16)=HresRenter(1)/real(nAgent)
      output(t,17)=Hinv(1)/real(nAgent)
      output(t,18)=HresRenter(2)/real(nAgent)
      output(t,19)=Hinv(2)/real(nAgent)
      output(t,20)=Pension
      output(t,21)=Bequest
      output(t,22)=HresRC(1)/real(nAgent)
      output(t,23)=HresRC(2)/real(nAgent)
      output(t,24)=RCprob(1)
      output(t,25)=RCprob(2)
      output(t,26)=PHavg(1)
      output(t,27)=PHavg(2)
      if(NumRetired.ge.1) then
       output(t,28)=output(t,2)*output(t,12)*taxss/real(NumRetired)
      else
       output(t,28)=0.0
      end if
      output(t,29)=PropTaxIncome
      output(t,30)=ProfitC
      output(t,31)=ProfitLOC1
      output(t,32)=ProfitLOC2
      output(t,33)=TaxableIncomeAvg
      output(t,34)=HSVgovSurplus
      output(t,35)=HSVfracPay
      output(t,36)=HSVmargRate
      output(t,37)=HoursDemandLOC1
      output(t,38)=HoursDemandLOC2

      tempR1=1.0-(Hdem(1)/HBARloc1(iHF))
      tempR2=1.0-(Hdem(2)/HBARloc2(iHF))

      i=1

      write(6,'(i6,i4,f9.5,f9.5,f9.5,f10.6,f10.6,f9.5,f8.4,f8.4,f8.4,
     1 f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,
     1 i4,i3,i4,f8.4,f8.4,i4,f8.4,f8.4,f8.4,f8.4,f8.4,i5,i5)')
     1 t,iHF,Wage,Rent(1),Rent(2),RP1,RP2,RCprob(1)+RCprob(2),
     1 Hours/real(nAgent),HoursDemand/real(nAgent),
     1 Hdem(1),H1/real(nAgent),Hdem(2),H2/real(nAgent),
     1 HresRenter(1)/real(nAgent),
     1 tempR3*(1.0-HFVgrid(iHF,1))+(Hinv(1)/real(nAgent)),
     1 HresRenter(2)/real(nAgent),
     1 tempR4*(1.0-HFVgrid(iHF,2))+(Hinv(2)/real(nAgent)),
     1 HresRC(1)/real(nAgent),RCshare(1,iHF)*(Hinv(1)/real(nAgent)),
     1 HresRC(2)/real(nAgent),RCshare(2,iHF)*(Hinv(2)/real(nAgent)),
     1 AgeInd(i),iZind(i),LOCind(i),NWind(i),BnextInd(i),
     1 RenterInd(i),HresInd(i),Hind(i),Cind(i),
     1 PHavg(1)*tempR1/Wage,PHavg(2)*tempR2/Wage,iClMkt,iClMktAlt
!      write(6,'(f8.4,f8.4,f8.4,f8.4,f8.4,f8.4)')
!     1 Cind(i),HresInd(i),HresInd(i)*Rent(1),
!     1 HoursInd(i),
!     1     1.0-(alphaN/alphaC)*(1.0/Wage)*Cind(i),
!     1 HoursInd(i)*Wage-Cind(i)-HresInd(i)*Rent(1)




      end do !t

      call Beliefs(nHF,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,
     1           Wagegrid,Rent1grid,Rent2grid,RP1grid,RP2grid,
     1           H1grid,H2grid,TotYears,taxss,output,nRegr,
     1           outputBeq,nBeqDist)

      do i=1,nAge
!       write(6,'(i4,f9.3,f9.3,f9.3,f9.3,f9.3,f9.3,f9.3,f9.3,
!     1           f9.3,f9.3,f9.3,f9.3)')
!     1  i,(NWbound((i-1)*nDZ+tempI1,1),tempI1=1,nDZ),
!     2    (NWbound((i-1)*nDZ+tempI1,2),tempI1=1,nDZ)
       do tempI1=1,nDZ
        NWbound((i-1)*nDZ+tempI1,1)=0.25*NWbound((i-1)*nDZ+tempI1,1)+
     1                              0.75*NWboundOld((i-1)*nDZ+tempI1,1)
        NWbound((i-1)*nDZ+tempI1,2)=0.25*NWbound((i-1)*nDZ+tempI1,2)+
     1                              0.75*NWboundOld((i-1)*nDZ+tempI1,2)
       end do
      end do

      do t=1,TotYears
       do i=1,50
        if(abs(output(t,i)).gt.10000000) output(t,i)=0
       end do
      end do
      
      write(6,*) 'outside'
      write(6,*) RCshare(1,1),RCshare(2,1),RCshare(1,2),RCshare(2,2)
      write(6,*) RCrentred(1,1),RCrentred(2,1),RCrentred(1,2),
     1 RCrentred(2,2)
      write(6,*) RCinccut(1,1),RCinccut(2,1),RCinccut(1,2),RCinccut(2,2)
      write(6,*) RChsize(1,1),RChsize(2,1),RChsize(1,2),RChsize(2,2)
      write(6,*) RCprobStay(1),RCprobStay(2),kappa2,kappa3,HresMin

      call writedata(NWbound,'NWbnd0.txt',nDZ*nAge,2,nDZ*nAge,2)
      call writeoutput(output,'output00.m',TotYears,50,TotYears,50)
      call writedata1(OutputWelf,'output01.m',TotYears*nAgent0,15,
     1                                       TotYears*nAgent0,15,
     1 nHF,nDZ,nLOC,nAge,nRet,HFgrid0,HFgrid1,HFVgrid,DZgrid,SSIdist,
     1 RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,PriceBond,
     1 taxss,taxprop,taxpropOOT,gamma0,alphaC,alphaH,alphaN,
     1 ElastCH,ElastCN,chi0,HoursMin,deprH,deprINV0,
     1 TrProbDZ,tau0,lambda0,tauBase,lambdaBase,
     1 CommCost,CommCostFin,beta0,BetaRel,
     1 Z1shiftCut,Z1shiftAll,Z1shiftSize,thetaRes,thetaInv,
     1 HresMin,RCshare,RCrentred,RCinccut,RChsize,RCprobStay,kappa2,
     1 kappa3,RCsubs,ProfitRedist)
      call writeoutput(outputErr,'output02.m',TotYears,7,TotYears,7)

      end

!--------------------------------------------------------------
!This creates beliefs by running regressions
      SUBROUTINE Beliefs(nHF,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,
     1           Wagegrid,Rent1grid,Rent2grid,RP1grid,RP2grid,
     1           H1grid,H2grid,TotYears,taxss,output,nRegr,
     1           outputBeq,nBeqDist)
      implicit none
      integer nHF,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2
      integer iHF,iHFnext,TotYears,t,i,j,ii,iRegression,nRegr,nBeqDist
      real output(TotYears,50),Ytemp(TotYears,1),Xtemp(TotYears,12)
      real coefs(12),wo,taxss,tempR1,tempR2
      integer columnsIn(12),tempI1
      real WageGrid(nWage),Rent1Grid(nRent1),Rent2Grid(nRent2)
      real RP1grid(nRP1),RP2grid(nRP2),H1grid(nH1),H2grid(nH2)
      real Regcoefs1(nRegr,nHF*nHF),Regcoefs2(nRegr,nHF*nHF)
      real Regcoefs3(nRegr,nHF*nHF),Regcoefs4(nRegr,nHF*nHF)
      real Regcoefs5(nRegr,nHF*nHF),Regcoefs6(nRegr,nHF*nHF)
      real Regcoefs7(nRegr,nHF*nHF),Regcoefs0(nRegr,nHF*nHF)
      real Regcoefs8(nRegr,nHF*nHF),Regcoefs9(nRegr,nHF*nHF)
      real Regcoefs10(nRegr,nHF*nHF),Regcoefs11(nRegr,nHF*nHF)
      real RegcoefsOld11(nRegr,nHF*nHF),RegcoefsOld10(nRegr,nHF*nHF)
      real RegcoefsOld9(nRegr,nHF*nHF),RegcoefsOld8(nRegr,nHF*nHF)
      real RegcoefsOld1(nRegr,nHF*nHF),RegcoefsOld2(nRegr,nHF*nHF)
      real RegcoefsOld3(nRegr,nHF*nHF),RegcoefsOld4(nRegr,nHF*nHF)
      real RegcoefsOld5(nRegr,nHF*nHF),RegcoefsOld6(nRegr,nHF*nHF)
      real RegcoefsOld7(nRegr,nHF*nHF),RegcoefsOld0(nRegr,nHF*nHF)
      real RegcoefsMinOld(nRegr,nHF*nHF),RegcoefsMin(nRegr,nHF*nHF)
      real RegcoefsMaxOld(nRegr,nHF*nHF),RegcoefsMax(nRegr,nHF*nHF)
      real outputBeq(TotYears,nBeqDist*2)
      double precision tempF1
      real RegCoefsBeqMin(nBeqDist*2,nHF*nHF)
      real RegCoefsBeqMinOld(nBeqDist*2,nHF*nHF)
      real RegCoefsBeqMax(nBeqDist*2,nHF*nHF)
      real RegCoefsBeqMaxOld(nBeqDist*2,nHF*nHF)
      real RegcoefsBeq0(nBeqDist*2,nHF*nHF)
      real RegcoefsBeqOld0(nBeqDist*2,nHF*nHF)
      real RegcoefsBeq1(nBeqDist*2,nHF*nHF)
      real RegcoefsBeqOld1(nBeqDist*2,nHF*nHF)

      call readdata(RegcoefsOld0,'Coef00.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld1,'Coef01.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld2,'Coef02.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld3,'Coef03.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld4,'Coef04.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld5,'Coef05.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld6,'Coef06.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld7,'Coef07.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld8,'Coef08.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld9,'Coef09.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld10,'Coef10.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsOld11,'Coef11.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsMinOld,'CoefMn.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)
      call readdata(RegcoefsMaxOld,'CoefMx.txt',
     1              nRegr,nHF*nHF,nRegr,nHF*nHF)

      call readdata(RegcoefsBeqOld0,'CoefB0.txt',2*nBeqDist,nHF*nHF,
     1                                           2*nBeqDist,nHF*nHF)
      call readdata(RegcoefsBeqOld1,'CoefB1.txt',2*nBeqDist,nHF*nHF,
     1                                           2*nBeqDist,nHF*nHF)
      call readdata(RegcoefsBeqMinOld,'CoefBn.txt',
     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)
      call readdata(RegcoefsBeqMaxOld,'CoefBx.txt',
     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)

      wo=0.9

      do iRegression=1,nRegr

      do iHF=1,nHF
      do iHFnext=1,nHF
       do t=1,TotYears
        Ytemp(t,1)=0
        do i=1,12
         Xtemp(t,i)=0
        end do
       end do
       i=0
       do t=101,TotYears-1
        if((nint(output(t,1)).eq.iHF.and.
     1      nint(output(t+1,1)).eq.iHFnext).or.
     1     (nint(output(t,1)).eq.iHF.and.iRegression.eq.6).or.
     1     (nint(output(t,1)).eq.iHF.and.iRegression.eq.7).or.
     1     (nint(output(t,1)).eq.iHF.and.iRegression.eq.9).or.
     1     (nint(output(t,1)).eq.iHF.and.iRegression.eq.10).or.
     1      iRegression.eq.13) then
         i=i+1
         Ytemp(i,1)=output(t+1,1+iRegression)
         if(iRegression.eq.9) Ytemp(i,1)=output(t,24)  !probability of receiving rent control in zone1
         if(iRegression.eq.10) Ytemp(i,1)=output(t,25)  !probability of receiving rent control in zone2
         if(iRegression.eq.11) then
          if(output(t,14).gt.0.001) then
           Ytemp(i,1)=
     1         (output(t,14)-output(t,16))/output(t,14)! share owned in zone1 !output(t,26)  !average price in zone1
          else
           Ytemp(i,1)=0
          end if
         end if
         if(iRegression.eq.12) then
          if(output(t,15).gt.0.001) then
           Ytemp(i,1)=
     1         (output(t,15)-output(t,18))/output(t,15)! share owned in zone1 !output(t,27)  !average price in zone2
          else
           Ytemp(i,1)=0
          end if
         end if
         if(iRegression.eq.13) Ytemp(i,1)=output(t,28)
         Xtemp(i,1)=1.0
         Xtemp(i,2)=output(t,2)
         Xtemp(i,3)=output(t,3)
         Xtemp(i,4)=output(t,4)
         Xtemp(i,5)=output(t,5)
         Xtemp(i,6)=output(t,6)
         Xtemp(i,7)=output(t,7)
         Xtemp(i,8)=output(t,8)
         Xtemp(i,9)=0.5*(output(t,3)+output(t,4))
         Xtemp(i,10)=0.5*(output(t,5)+output(t,6))
         Xtemp(i,11)=0.5*(output(t,7)+output(t,8))
         Xtemp(i,12)=0.0
        end if
       end do

       tempR1=-1000000000
       tempR2=1000000000
       do j=1,i
        if(Ytemp(j,1).gt.tempR1) tempR1=Ytemp(j,1)
        if(Ytemp(j,1).lt.tempR2) tempR2=Ytemp(j,1)
       end do
       if(tempR2.lt.0) then
        tempR2=tempR2*1.1
       else
        tempR2=tempR2*0.9
       end if
       if(tempR1.lt.0) then
        tempR1=tempR1*0.9
       else
        tempR1=tempR1*1.1
       end if
       RegcoefsMin(iRegression,(iHF-1)*nHF+iHFnext)=tempR2*(1.0-wo)+
     1        wo*RegcoefsMinOld(iRegression,(iHF-1)*nHF+iHFnext)
       RegcoefsMax(iRegression,(iHF-1)*nHF+iHFnext)=tempR1*(1.0-wo)+
     1        wo*RegcoefsMaxOld(iRegression,(iHF-1)*nHF+iHFnext)

       do j=1,12
        coefs(j)=0.0
       end do
       if(i.gt.20) then
        ColumnsIn(1)=1
        ColumnsIn(2)=1+iRegression
        if(iRegression.le.3) then
         ColumnsIn(3)=11
        else
         ColumnsIn(3)=0
        end if
        if(iRegression.eq.8.or.iRegression.eq.9.or.
     1     iRegression.eq.10) then
         ColumnsIn(2)=2
         ColumnsIn(3)=0
        end if
        if(iRegression.eq.11) then
         ColumnsIn(2)=2
         ColumnsIn(3)=3
        end if
        if(iRegression.eq.12) then
         ColumnsIn(2)=2
         ColumnsIn(3)=4
        end if
        if(iRegression.eq.13) then
         ColumnsIn(2)=0
         ColumnsIn(3)=0
        end if
        ColumnsIn(4)=0
        ColumnsIn(5)=0
        ColumnsIn(6)=0
        ColumnsIn(7)=0
        ColumnsIn(8)=0
        ColumnsIn(9)=0
        ColumnsIn(10)=0
        ColumnsIn(11)=0
        ColumnsIn(12)=0
        tempI1=0
        do j=1,12
         if(ColumnsIn(j).gt.0) tempI1=tempI1+1
        end do
        call regress(Ytemp,Xtemp,TotYears,i,12,tempI1,ColumnsIn,
     1               coefs,tempF1)
        write(6,'(i3,i3,i3,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,
     1    f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f11.5,f11.5,f11.5)')
     1  iRegression,iHF,iHFnext,(coefs(ii),ii=1,12),
     1  RegcoefsMin(iRegression,(iHF-1)*nHF+iHFnext),
     1  RegcoefsMax(iRegression,(iHF-1)*nHF+iHFnext),
     1  tempF1
       else
        if(i.gt.0) then
         tempR1=0.0
         do t=1,i
          tempR1=tempR1+Ytemp(t,1)
         end do
         coefs(1)=tempR1/real(i)
        else
         j=1
         if(iRegression.eq.1) coefs(1)=WageGrid(j)
         if(iRegression.eq.2) coefs(1)=Rent1grid(j)
         if(iRegression.eq.3) coefs(1)=Rent2grid(j)
         if(iRegression.eq.4) coefs(1)=RP1grid(j)
         if(iRegression.eq.5) coefs(1)=RP2grid(j)
         if(iRegression.eq.6) coefs(1)=H1grid(j)
         if(iRegression.eq.7) coefs(1)=H2grid(j)
         if(iRegression.eq.8) coefs(1)=0
         if(iRegression.eq.9) coefs(1)=0
         if(iRegression.eq.10) coefs(1)=0
         if(iRegression.eq.11) coefs(1)=1.0
         if(iRegression.eq.12) coefs(1)=1.0
         if(iRegression.eq.13) coefs(1)=0.0
        end if
        do j=2,12
         coefs(j)=0.0
        end do
       end if

       do j=1,12
        if(abs(coefs(j)).gt.99.0) then
         write(6,'(a,i5,i5,i5,f12.4)')
     1 'Coef Problem ',iRegression,j,i,coefs(j)
        end if
        if(coefs(j).gt.100.0) coefs(j)=100.0
        if(coefs(j).lt.-100.0) coefs(j)=-100.0
       end do

       Regcoefs0(iRegression,(iHF-1)*nHF+iHFnext)=coefs(1)*(1.0-wo)+
     1  wo*RegcoefsOld0(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs1(iRegression,(iHF-1)*nHF+iHFnext)=coefs(2)*(1.0-wo)+
     1  wo*RegcoefsOld1(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs2(iRegression,(iHF-1)*nHF+iHFnext)=coefs(3)*(1.0-wo)+
     1  wo*RegcoefsOld2(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs3(iRegression,(iHF-1)*nHF+iHFnext)=coefs(4)*(1.0-wo)+
     1  wo*RegcoefsOld3(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs4(iRegression,(iHF-1)*nHF+iHFnext)=coefs(5)*(1.0-wo)+
     1  wo*RegcoefsOld4(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs5(iRegression,(iHF-1)*nHF+iHFnext)=coefs(6)*(1.0-wo)+
     1  wo*RegcoefsOld5(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs6(iRegression,(iHF-1)*nHF+iHFnext)=coefs(7)*(1.0-wo)+
     1  wo*RegcoefsOld6(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs7(iRegression,(iHF-1)*nHF+iHFnext)=coefs(8)*(1.0-wo)+
     1  wo*RegcoefsOld7(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs8(iRegression,(iHF-1)*nHF+iHFnext)=coefs(9)*(1.0-wo)+
     1  wo*RegcoefsOld8(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs9(iRegression,(iHF-1)*nHF+iHFnext)=coefs(10)*(1.0-wo)+
     1  wo*RegcoefsOld9(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs10(iRegression,(iHF-1)*nHF+iHFnext)=coefs(11)*(1.0-wo)+
     1  wo*RegcoefsOld10(iRegression,(iHF-1)*nHF+iHFnext)
       Regcoefs11(iRegression,(iHF-1)*nHF+iHFnext)=coefs(12)*(1.0-wo)+
     1  wo*RegcoefsOld11(iRegression,(iHF-1)*nHF+iHFnext)
      end do !iHFnext
      end do !iHF

      end do !iRegression

!Regression takes form Y=B0+B1*Wage(t)+B2*Rent1(t)+B3*Rent2(t)+B4*RP1(t)+B5*RP2(t)+B6*H1(t)+B7*H2(t)
!There are 8 regression coefficients - each variable Regcoefs0,Regcoefs1,... Regcoefs7 is a regression coefficient
!There are 8 variables to be predicted (8 regressions) - Wage(t+1),Rent1(t+1),Rent2(t+1),RP1(t+1),RP2(t+1),H1(t+1),H2(t+1),Pension(t) --> these are the first entry of Regcoefs
!For each regression coefficient and each variable, there are 4 separate regressions: conditional on (iHF,iHFnext) --> these are the second entry of Regcoefs
      call writedata(Regcoefs0,'Coef00.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs1,'Coef01.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs2,'Coef02.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs3,'Coef03.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs4,'Coef04.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs5,'Coef05.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs6,'Coef06.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs7,'Coef07.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs8,'Coef08.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs9,'Coef09.txt',nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs10,'Coef10.txt',
     1 nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(Regcoefs11,'Coef11.txt',
     1 nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(RegcoefsMin,'CoefMn.txt',
     1 nRegr,nHF*nHF,nRegr,nHF*nHF)
      call writedata(RegcoefsMax,'CoefMx.txt',
     1 nRegr,nHF*nHF,nRegr,nHF*nHF)

!Create beliefs about bequests
!When there are bequesters and non-bequesters, need separate beliefs for each group, this is why nBeqDist*2
!If fracBeq=0, then still computing beliefs as if there are two groups, but the second set will be ignored
      do iRegression=1,nBeqDist*2

      do iHF=1,nHF
      do iHFnext=1,nHF
       do t=1,TotYears
        Ytemp(t,1)=0
        do i=1,12
         Xtemp(t,i)=0
        end do
       end do
       i=0
       do t=101,TotYears-1
        if(nint(output(t,1)).eq.iHF.and.
     1     nint(output(t+1,1)).eq.iHFnext) then
         i=i+1
         Ytemp(i,1)=outputBeq(t+1,iRegression)
         Xtemp(i,1)=1.0
         Xtemp(i,2)=output(t,2)
         Xtemp(i,3)=output(t,3)
         Xtemp(i,4)=output(t,4)
         Xtemp(i,5)=output(t,5)
         Xtemp(i,6)=output(t,6)
         Xtemp(i,7)=output(t,7)
         Xtemp(i,8)=output(t,8)
         Xtemp(i,9)=0.5*(output(t,3)+output(t,4))
         Xtemp(i,10)=0.5*(output(t,5)+output(t,6))
         Xtemp(i,11)=0.5*(output(t,7)+output(t,8))
         Xtemp(i,12)=0.0
        end if
       end do

       tempR1=-1000000000
       tempR2=1000000000
       do j=1,i
        if(Ytemp(j,1).gt.tempR1) tempR1=Ytemp(j,1)
        if(Ytemp(j,1).lt.tempR2) tempR2=Ytemp(j,1)
       end do
       if(tempR2.lt.0) then
        tempR2=tempR2*1.1
       else
        tempR2=tempR2*0.9
       end if
       if(tempR1.lt.0) then
        tempR1=tempR1*0.9
       else
        tempR1=tempR1*1.1
       end if
       RegcoefsBeqMin(iRegression,(iHF-1)*nHF+iHFnext)=tempR2
       RegcoefsBeqMax(iRegression,(iHF-1)*nHF+iHFnext)=tempR1

       do j=1,12
        coefs(j)=0.0
       end do
       if(i.gt.20) then
        ColumnsIn(1)=1
        ColumnsIn(2)=2
        ColumnsIn(3)=0
        ColumnsIn(4)=0
        ColumnsIn(5)=0
        ColumnsIn(6)=0
        ColumnsIn(7)=0
        ColumnsIn(8)=0
        ColumnsIn(9)=0
        ColumnsIn(10)=0
        ColumnsIn(11)=0
        ColumnsIn(12)=0
        tempI1=0
        do j=1,12
         if(ColumnsIn(j).gt.0) tempI1=tempI1+1
        end do
        call regress(Ytemp,Xtemp,TotYears,i,12,tempI1,ColumnsIn,
     1               coefs,tempF1)
        write(6,'(i3,i3,i3,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,
     1     f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f11.5,f11.5,f11.5)')
     1  iRegression,iHF,iHFnext,(coefs(i),i=1,12),
     1  RegcoefsBeqMin(iRegression,(iHF-1)*nHF+iHFnext),
     1  RegcoefsBeqMax(iRegression,(iHF-1)*nHF+iHFnext),tempF1
       else
        if(i.gt.0) then
         tempR1=0.0
         do t=1,i
          tempR1=tempR1+Ytemp(t,1)
         end do
         coefs(1)=tempR1/real(i)
        else
         coefs(1)=0
        end if
       end if

       RegcoefsBeq0(iRegression,(iHF-1)*nHF+iHFnext)=
     1 (1.0-wo)*coefs(1)+
     1  wo*RegcoefsBeqOld0(iRegression,(iHF-1)*nHF+iHFnext)
       RegcoefsBeq1(iRegression,(iHF-1)*nHF+iHFnext)=
     1 (1.0-wo)*coefs(2)+
     1  wo*RegcoefsBeqOld1(iRegression,(iHF-1)*nHF+iHFnext)
       RegcoefsBeqMin(iRegression,(iHF-1)*nHF+iHFnext)=
     1       (1.0-wo)*RegcoefsBeqMin(iRegression,(iHF-1)*nHF+iHFnext)+
     1        wo*RegcoefsBeqMinOld(iRegression,(iHF-1)*nHF+iHFnext)
       RegcoefsBeqMax(iRegression,(iHF-1)*nHF+iHFnext)=
     1       (1.0-wo)*RegcoefsBeqMax(iRegression,(iHF-1)*nHF+iHFnext)+
     1        wo*RegcoefsBeqMaxOld(iRegression,(iHF-1)*nHF+iHFnext)

      end do
      end do

      end do

      call writedata(RegcoefsBeq0,'CoefB0.txt',2*nBeqDist,nHF*nHF,
     1                                         2*nBeqDist,nHF*nHF)
      call writedata(RegcoefsBeq1,'CoefB1.txt',2*nBeqDist,nHF*nHF,
     1                                         2*nBeqDist,nHF*nHF)
      call writedata(RegcoefsBeqMin,'CoefBn.txt',
     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)
      call writedata(RegcoefsBeqMax,'CoefBx.txt',
     1              2*nBeqDist,nHF*nHF,2*nBeqDist,nHF*nHF)

      end

!------------------------------------------------------------------------
!nAgent0 is the actual number of agents (ie 2000)
!nAgent is the number of agents for whom we are computing output (ie 500)
!note that in the main code, nAgent and nAgent0 are reverse from computemoments1
      SUBROUTINE computemoments1(TotYears,nAgent,nAgent0,
     1 nLOC,nDZ,nAge,nRet,nHF,DZgrid,SSIdist,AgeProd,
     1 RCinccut,RChsize,RCrentred,RCshare,PriceBond,deprH,
     1 taxss,taxprop,taxpropOOT,RTSH0loc1,RTSH0loc2,HBARloc1,HBARloc2,
     1 NumBorn,HFgrid0,HFgrid1,output,outputWelf,outputErr,
     1 popShare1,fracRet,rentDiff,incDiff,MedIncomeWorker,RCshareRent,
     1 RCshareAll,fracSameRC,RCsubs,ProfitRedist,lambda0,tau0,
     1 lambdaBase,tauBase)
      implicit none
      integer TotYears,nAgent,nAgent0,nLOC,nDZ,nAge,nRet,nHF
      integer t,i,j,j1,j2,j3,j4,iLOC,iHF,flagConstRC
      real RTSH0loc1,RTSH0loc2,HBARloc1(nHF),HBARloc2(nHF)
      real DZgrid(nAge,nDZ),SSIdist(nDZ),AgeProd(nAge)
      real taxprop(nHF,nLOC),taxpropOOT(nLOC),deprH(nLOC),deprHAvg
      real taxss,PriceBond
      real RCavgrent(nLOC,nHF),RCshare(nLOC,nHF),RCrentred(nLOC,nHF)
      real RChsize(nLOC,nHF),RCinccut(nLOC,nHF)
      real NumBorn,HFgrid0(nHF,nLOC),HFgrid1(nHF,nLOC),LaborIncome
      real output(TotYears,50),outputWelf(TotYears*nAgent,15)
      real outputErr(TotYears,7)
      real Rent(1+nLOC),RentAvg(1+nLOC),PriceMkt(1+nLOC)
      real HoursAvg(1+nLOC),HoursAvgTemp(1+nLOC)
      real PriceAvg(1+nLOC),WageAvg(1+nLOC),HrentAvg(1+nLOC)
      real NWavg(1+nLOC),NWworkavg(1+nLOC),Havg(1+nLOC),HRCavg(1+nLOC)
      real WageMed,Wage,GiniLIwork,GiniNWwork,GiniNW,BeqAvg
      real RentMkt(1+nLOC),HavgTemp(1+nLOC),Htot(1+nLOC)
      real WageAvgTemp(1+nLOC),NWavgTemp(1+nLOC),NWworkavgTemp(1+nLOC)
      real HrentAvgTemp(1+nLOC),HRCavgTemp(1+nLOC),PropTaxIncomeAvg(nHF)
      real HouseValueAvg(nHF),HouseValueForeignAvg(nHF)
      real LIworkSample(10000,1),NWworkSample(10000,1)
      real NWsample(10000,1)
      integer SortIndex(10000,1)
      real tempR1,tempR2,tempR3,tempR4,tempR5,tempR6,tempR7
      integer tempI1,tempI2,tempI3,tempI4,tempI5,tempI6
      real countWork(1+nLOC),countAll(1+nLOC),countAllRent(1+nLOC)
      real countAllRC(1+nLOC),countAllRentTemp(1+nLOC),countHF(nHF)
      real countWorkTemp(1+nLOC),countAllTemp(1+nLOC)
      real countAllRCTemp(1+nLOC)
      real countAllRentCond(1+nLOC,nHF),countAllRCCond(1+nLOC,nHF)
      integer countSample,countWorkSample
      real popShare1,fracRet(nLOC),rentDiff,incDiff
      real AvgIncomeWorker,MedIncomeWorker,RCshareRent(nLOC,nHF)
      real TaxableIncomeAvg,HSVgovSurplus,HSVfracPay,HSVmargRate
      real countAllCond(1+nLOC,nHF),RCshareAll(nLOC,nHF)
      real countRC,countSameRC,fracSameRC,RCsubs(nLOC,nHF),RCShareSubs
      real RCavgRentDev(nLOC,nHF),Subs(1+nLOC),WageBill1,WageBill2
      real HresMinVoucher,HresMinVoucherTot
      real VoucherExpense,VoucherExpenseTot
      real r0,ProfitRedist(3),Profit,TaxableIncome,HSVtax,HSVtaxBase
      real lambda0(nHF),tau0(nHF),lambdaBase,tauBase

      r0=1.0-PriceBond

      do iLOC=1,nLOC
       do iHF=1,nHF
        RCavgrent(iLOC,iHF)=1.0-RCshare(iLOC,iHF)+
     1                      RCshare(iLOC,iHF)*(1.0-RCrentred(iLOC,iHF))
        RCavgrentDev(iLOC,iHF)=1.0-RCshare(iLOC,iHF)+
     1RCshare(iLOC,iHF)*(1.0-RCrentred(iLOC,iHF))*(1.0+RCsubs(iLOC,iHF))
       end do
      end do

      do i=1,1+nLOC
       RentMkt(i)=0
       RentAvg(i)=0
       PriceMkt(i)=0
       PriceAvg(i)=0
       WageAvg(i)=0
       HoursAvg(i)=0
       NWavg(i)=0
       NWworkavg(i)=0
       Htot(i)=0
       Havg(i)=0
       HrentAvg(i)=0
       HRCavg(i)=0
       countAll(i)=0
       countAllRent(i)=0
       countAllRC(i)=0
       countWork(i)=0
       do iHF=1,nHF
        countAllRentCond(i,iHF)=0
        countAllRentCond(i,iHF)=0
        countAllRCCond(i,iHF)=0
        countAllRCCond(i,iHF)=0
        countAllCond(i,iHF)=0
        countAllCond(i,iHF)=0
       end do
      end do
      do i=1,nHF
       HouseValueAvg(i)=0
       HouseValueForeignAvg(i)=0
       PropTaxIncomeAvg(i)=0
       countHF(i)=0
      end do
      BeqAvg=0
      countSample=0
      countWorkSample=0
      TaxableIncomeAvg=0
      HSVgovSurplus=0
      HSVfracPay=0
      HSVmargRate=0
      fracSameRC=0
      WageBill1=0
      WageBill2=0
      HresMinVoucherTot=0
      VoucherExpenseTot=0
      do t=101,TotYears
       iHF=nint(output(t,1))
       Wage=output(t,2)
       countHF(iHF)=countHF(iHF)+1.0
       PropTaxIncomeAvg(iHF)=PropTaxIncomeAvg(iHF)+output(t,29)
       HouseValueAvg(iHF)=HouseValueAvg(iHF)+
     1  (output(t,14)*output(t,10)+output(t,15)*output(t,11))
       HouseValueForeignAvg(iHF)=HouseValueForeignAvg(iHF)+
     1  output(t,10)*
     1  exp(HFgrid0(iHF,1)-HFgrid1(iHF,1)*
     1      log(output(t,10)*(1.0+taxpropOOT(1))))+
     1  output(t,11)*
     1  exp(HFgrid0(iHF,2)-HFgrid1(iHF,2)*
     1      log(output(t,11)*(1.0+taxpropOOT(2))))
       RentMkt(1)=RentMkt(1)+
     1  (output(t,3)*(output(t,14)-output(t,22))+
     1   output(t,4)*(output(t,15)-output(t,23)))/
     1  (output(t,14)+output(t,15)-output(t,22)-output(t,23))
       RentMkt(2)=RentMkt(2)+output(t,3)
       RentMkt(3)=RentMkt(3)+output(t,4)
       tempR1=output(t,3)*
     1       (1.0-(output(t,22)/output(t,14))*(1.0-RCrentred(1,iHF)))
       tempR2=output(t,4)*
     1       (1.0-(output(t,23)/output(t,15))*(1.0-RCrentred(2,iHF)))
       RentAvg(1)=RentAvg(1)+(output(t,14)*tempR1+output(t,15)*tempR2)/
     1                       (output(t,14)+output(t,15))
       RentAvg(2)=RentAvg(2)+tempR1
       RentAvg(3)=RentAvg(3)+tempR2
       PriceMkt(1)=PriceMkt(1)+
     1         (output(t,10)*(output(t,14)-output(t,22))+
     1          output(t,11)*(output(t,15)-output(t,23)))/
     1         (output(t,14)+output(t,15)-output(t,22)-output(t,23))
       PriceMkt(2)=PriceMkt(2)+output(t,10)
       PriceMkt(3)=PriceMkt(3)+output(t,11)
       tempR1=output(t,10)*
     1       (1.0-(output(t,22)/output(t,14))*(1.0-RCrentred(1,iHF)))
       tempR2=output(t,11)*
     1       (1.0-(output(t,23)/output(t,15))*(1.0-RCrentred(2,iHF)))
       PriceAvg(1)=PriceAvg(1)+
     1            (output(t,14)*tempR1+output(t,15)*tempR2)/
     1            (output(t,14)+output(t,15))
       PriceAvg(2)=PriceAvg(2)+tempR1
       PriceAvg(3)=PriceAvg(3)+tempR2
       Htot(1)=Htot(1)+output(t,14)+output(t,15)
       Htot(2)=Htot(2)+output(t,14)
       Htot(3)=Htot(3)+output(t,15)
       BeqAvg=BeqAvg+output(t,9)
       TaxableIncomeAvg=TaxableIncomeAvg+output(t,33)
       HSVgovSurplus=HSVgovSurplus+output(t,34)
       HSVfracPay=HSVfracPay+output(t,35)
       HSVmargRate=HSVmargRate+output(t,36)
       WageBill1=WageBill1+Wage*output(t,37)/real(nAgent0) !wage bill per firm in construction sector in each zone (nFirm=nAgent)
       WageBill2=WageBill2+Wage*output(t,38)/real(nAgent0)
       do i=1,1+nLOC
        HoursAvgTemp(i)=0
        WageAvgTemp(i)=0
        NWavgTemp(i)=0
        NWworkavgTemp(i)=0
        HavgTemp(i)=0
        HrentAvgTemp(i)=0
        HRCavgTemp(i)=0
        countWorkTemp(i)=0
        countAllTemp(i)=0
        countAllRentTemp(i)=0
        countAllRCTemp(i)=0
        countRC=0
        countSameRC=0
       end do
       do i=1,nAgent
        j=(t-1)*nAgent+i
        j1=(t-1-1)*nAgent+i
        j2=(t-1-2)*nAgent+i
        j3=(t-1-3)*nAgent+i
        j4=(t-1-4)*nAgent+i

        if (nint(outputWelf(j,12)).eq.3) then !agent currently in RC
         countRC=countRC+1
         if ((outputWelf(j,3).gt.outputWelf(j1,3).and. !same agent for 5 consecutive periods (didn't die)
     1    outputWelf(j1,3).gt.outputWelf(j2,3).and.
     1    outputWelf(j2,3).gt.outputWelf(j3,3)).and.
     1    outputWelf(j3,3).gt.outputWelf(j4,3)) then
          if ((outputWelf(j,12).eq.3.and.outputWelf(j1,12).eq.3.and. !agent been in RC
     1     outputWelf(j2,12).eq.3.and.outputWelf(j3,12).eq.3.and.
     1     outputWelf(j4,12).eq.3).and. !and same zone for >=5 consecutive periods
     1     ((outputWelf(j,5).eq.1.and.outputWelf(j1,5).eq.1.and.
     1     outputWelf(j2,5).eq.1.and.outputWelf(j3,5).eq.1.and.
     1     outputWelf(j4,5).eq.1).or.
     1     (outputWelf(j,5).eq.2.and.outputWelf(j1,5).eq.2.and.
     1     outputWelf(j2,5).eq.2.and.outputWelf(j3,5).eq.2.and.
     1     outputWelf(j4,5).eq.2))) then
           countSameRC=countSameRC+1
          end if
         end if
        end if

        LaborIncome=outputWelf(j,10)*Wage*
     1              outputWelf(j,11)*AgeProd(nint(outputWelf(j,3)))

        Profit=(output(t,30)*ProfitRedist(1)+output(t,31)*
     1       ProfitRedist(2)+output(t,32)*ProfitRedist(3))/real(nAgent0)
        TaxableIncome=r0*outputWelf(j,13)+Profit+LaborIncome
        HSVtax=TaxableIncome-
     1     lambda0(iHF)*(TaxableIncome**(1.0-tau0(iHF)))
        HSVtaxBase=TaxableIncome-
     1            lambdaBase*(TaxableIncome**(1.0-tauBase))
        if(HSVtax.lt.0.and.HSVtax.lt.HSVtaxBase) then
         VoucherExpense=HSVtaxBase-HSVtax
         if (outputWelf(j,5).eq.1) then
          HresMinVoucher=VoucherExpense/output(t,3)
         else
          HresMinVoucher=VoucherExpense/output(t,4)
         end if
        else
         HresMinVoucher=0.0
         VoucherExpense=0
        end if
        HresMinVoucherTot=HresMinVoucherTot+HresMinVoucher/real(nAgent)
        VoucherExpenseTot=VoucherExpenseTot+VoucherExpense/real(nAgent)

        if(countSample.lt.10000.and.mod(j,13).eq.0) then
         countSample=countSample+1
         NWsample(countSample,1)=outputWelf(j,13)
        end if
        if(nint(outputWelf(j,3)).le.nAge-nRet) then
         if(countWorkSample.lt.10000.and.mod(j,13).eq.0) then
          countWorkSample=countWorkSample+1
          LIworkSample(countWorkSample,1)=LaborIncome
          NWworkSample(countWorkSample,1)=outputWelf(j,13)
         end if
         countWorkTemp(1)=countWorkTemp(1)+1
         WageAvgTemp(1)=WageAvgTemp(1)+LaborIncome
         HoursAvgTemp(1)=HoursAvgTemp(1)+outputWelf(j,10)
         NWworkavgTemp(1)=NWworkavgTemp(1)+outputWelf(j,13)
         if(nint(outputWelf(j,5)).eq.1) then
          countWorkTemp(2)=countWorkTemp(2)+1
          WageAvgTemp(2)=WageAvgTemp(2)+LaborIncome
          HoursAvgTemp(2)=HoursAvgTemp(2)+outputWelf(j,10)
          NWworkavgTemp(2)=NWworkavgTemp(2)+outputWelf(j,13)
         end if
         if(nint(outputWelf(j,5)).eq.2) then
          countWorkTemp(3)=countWorkTemp(3)+1
          WageAvgTemp(3)=WageAvgTemp(3)+LaborIncome
          HoursAvgTemp(3)=HoursAvgTemp(3)+outputWelf(j,10)
          NWworkavgTemp(3)=NWworkavgTemp(3)+outputWelf(j,13)
         end if
        end if
        countAllTemp(1)=countAllTemp(1)+1
        NWavgTemp(1)=NWavgTemp(1)+outputWelf(j,13)
        HavgTemp(1)=HavgTemp(1)+outputWelf(j,9)
        countAllCond(1,iHF)=countAllCond(1,iHF)+1
        if(nint(outputWelf(j,12)).eq.1) then
         countAllRentCond(1,iHF)=countAllRentCond(1,iHF)+1
         countAllRentTemp(1)=countAllRentTemp(1)+1
         HrentAvgTemp(1)=HrentAvgTemp(1)+outputWelf(j,9)
        end if
        if(nint(outputWelf(j,12)).eq.3) then
         countAllRCCond(1,iHF)=countAllRCCond(1,iHF)+1
         countAllRCTemp(1)=countAllRCTemp(1)+1
         HRCavgTemp(1)=HRCavgTemp(1)+outputWelf(j,9)
        end if
        if(nint(outputWelf(j,5)).eq.1) then
         countAllCond(2,iHF)=countAllCond(2,iHF)+1
         countAllTemp(2)=countAllTemp(2)+1
         NWavgTemp(2)=NWavgTemp(2)+outputWelf(j,13)
         HavgTemp(2)=HavgTemp(2)+outputWelf(j,9)
         if(nint(outputWelf(j,12)).eq.1) then
          countAllRentCond(2,iHF)=countAllRentCond(2,iHF)+1
          countAllRentTemp(2)=countAllRentTemp(2)+1
          HrentAvgTemp(2)=HrentAvgTemp(2)+outputWelf(j,9)
         end if
         if(nint(outputWelf(j,12)).eq.3) then
          countAllRCCond(2,iHF)=countAllRCCond(2,iHF)+1
          countAllRCTemp(2)=countAllRCTemp(2)+1
          HRCavgTemp(2)=HRCavgTemp(2)+outputWelf(j,9)
         end if
        end if
        if(nint(outputWelf(j,5)).eq.2) then
         countAllCond(3,iHF)=countAllCond(3,iHF)+1
         countAllTemp(3)=countAllTemp(3)+1
         NWavgTemp(3)=NWavgTemp(3)+outputWelf(j,13)
         HavgTemp(3)=HavgTemp(3)+outputWelf(j,9)
         if(nint(outputWelf(j,12)).eq.1) then
          countAllRentCond(3,iHF)=countAllRentCond(3,iHF)+1
          countAllRentTemp(3)=countAllRentTemp(3)+1
          HrentAvgTemp(3)=HrentAvgTemp(3)+outputWelf(j,9)
         end if
         if(nint(outputWelf(j,12)).eq.3) then
          countAllRCCond(3,iHF)=countAllRCCond(3,iHF)+1
          countAllRCTemp(3)=countAllRCTemp(3)+1
          HRCavgTemp(3)=HRCavgTemp(3)+outputWelf(j,9)
         end if
        end if
       end do
       do i=1,1+nLOC
        WageAvg(i)=WageAvg(i)+WageAvgTemp(i)
        HoursAvg(i)=HoursAvg(i)+HoursAvgTemp(i)
        NWavg(i)=NWavg(i)+NWavgTemp(i)
        NWworkavg(i)=NWworkavg(i)+NWworkavgTemp(i)
        Havg(i)=Havg(i)+HavgTemp(i)
        HrentAvg(i)=HrentAvg(i)+HrentAvgTemp(i)
        HRCavg(i)=HRCavg(i)+HRCavgTemp(i)
        countAll(i)=countAll(i)+countAllTemp(i)
        countAllRent(i)=countAllRent(i)+countAllRentTemp(i)
        countAllRC(i)=countAllRC(i)+countAllRCTemp(i)
        countWork(i)=countWork(i)+countWorkTemp(i)
       end do
       fracSameRC=fracSameRC+countSameRC/countRC
      end do

      BeqAvg=BeqAvg/real(TotYears-100)
      TaxableIncomeAvg=TaxableIncomeAvg/real(TotYears-100)
      HSVgovSurplus=HSVgovSurplus/real(TotYears-100)
      HSVfracPay=HSVfracPay/real(TotYears-100)
      HSVmargRate=HSVmargRate/real(TotYears-100)
      fracSameRC=fracSameRC/real(TotYears-100)
      WageBill1=WageBill1/real(TotYears-100)
      WageBill2=WageBill2/real(TotYears-100)
      HresMinVoucherTot=HresMinVoucherTot/real(TotYears-100)
      VoucherExpenseTot=VoucherExpenseTot/real(TotYears-100)
      do i=1,1+nLOC
       RentAvg(i)=RentAvg(i)/real(TotYears-100)
       RentMkt(i)=RentMkt(i)/real(TotYears-100)
       PriceAvg(i)=PriceAvg(i)/real(TotYears-100)
       PriceMkt(i)=PriceMkt(i)/real(TotYears-100)
       Htot(i)=Htot(i)/real(TotYears-100)
       WageAvg(i)=WageAvg(i)/countWork(i)
       HoursAvg(i)=HoursAvg(i)/countWork(i)
       NWavg(i)=NWavg(i)/countAll(i)
       NWworkavg(i)=NWworkavg(i)/countWork(i)
       Havg(i)=Havg(i)/countAll(i)
       Hrentavg(i)=Hrentavg(i)/countAllRent(i)
       HRCavg(i)=HRCavg(i)/countAllRC(i)
       countAll(i)=countAll(i)/real(TotYears-100)
       countAllRent(i)=countAllRent(i)/real(TotYears-100)
       countAllRC(i)=countAllRC(i)/real(TotYears-100)
       countWork(i)=countWork(i)/real(TotYears-100)
      end do

      call sort(LIworkSample,10000,SortIndex)
      MedIncomeWorker=LIworkSample(5000,1)
      AvgIncomeWorker=WageAvg(1)
      popShare1=countAll(2)/countAll(1)
      fracRet(1)=(1.0-countWork(2)/countAll(2))
      fracRet(2)=(1.0-countWork(3)/countAll(3))
      incDiff=WageAvg(2)/WageAvg(3)
      rentDiff=RentMkt(2)/RentMkt(3)

      flagConstRC=0
      do i=1,nLOC
       if(abs(RCinccut(i,1)-RCinccut(i,2)).gt.0.0001.or.
     1    abs(RChsize(i,1)-RChsize(i,2)).gt.0.0001.or.
     1    abs(RCrentred(i,1)-RCrentred(i,2)).gt.0.0001.or.
     1    abs(RCshare(i,1)-RCshare(i,2)).gt.0.0001) flagConstRC=1
      end do

      do iHF=1,nHF
       if(flagConstRC.eq.1) then
        RCshareRent(1,iHF)=countAllRCCond(2,iHF)/
     1           (countAllRentCond(2,iHF)+countAllRCCond(2,iHF))
        RCshareRent(2,iHF)=countAllRCCond(3,iHF)/
     1           (countAllRentCond(3,iHF)+countAllRCCond(3,iHF))
        RCshareAll(1,iHF)=countAllRCCond(2,iHF)/countAllCond(2,iHF)
        RCshareAll(2,iHF)=countAllRCCond(3,iHF)/countAllCond(3,iHF)
       else
        RCshareRent(1,iHF)=(countAllRCCond(2,1)+countAllRCCond(2,2))/
     1                     (countAllRentCond(2,1)+countAllRCCond(2,1)+
     1                      countAllRentCond(2,2)+countAllRCCond(2,2))
        RCshareRent(2,iHF)=(countAllRCCond(3,1)+countAllRCCond(3,2))/
     1                     (countAllRentCond(3,1)+countAllRCCond(3,1)+
     1                      countAllRentCond(3,2)+countAllRCCond(3,2))
        RCshareAll(1,iHF)=(countAllRCCond(2,1)+countAllRCCond(2,2))/
     1   (countAllCond(2,1)+countAllCond(2,2))
        RCshareAll(2,iHF)=(countAllRCCond(3,1)+countAllRCCond(3,2))/
     1   (countAllCond(3,1)+countAllCond(3,2))
       end if
      end do

      call sort(NWsample,10000,SortIndex)
      tempR5=0
      tempR6=0
      do i=1,10000
       tempR5=tempR5+real(i)*NWsample(i,1)
       tempR6=tempR6+NWsample(i,1)
      end do
      GiniNW=((2.0*tempR5)/(10000.0*tempR6))-1.0
      call sort(NWworkSample,10000,SortIndex)
      tempR5=0
      tempR6=0
      do i=1,10000
       tempR5=tempR5+real(i)*NWworkSample(i,1)
       tempR6=tempR6+NWworkSample(i,1)
      end do
      GiniNWwork=((2.0*tempR5)/(10000.0*tempR6))-1.0
      call sort(LIworkSample,10000,SortIndex)
      tempR5=0
      tempR6=0
      do i=1,10000
       tempR5=tempR5+real(i)*LIworkSample(i,1)
       tempR6=tempR6+LIworkSample(i,1)
      end do
      GiniLIwork=((2.0*tempR5)/(10000.0*tempR6))-1.0

!average(market rent per square foot) (including only market units)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'Rent Mkt    ',
     1 RentMkt(1),RentMkt(2),RentMkt(3),RentMkt(2)/RentMkt(3)
!average(rent per square foot) (including all units)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'Rent Avg    ',
     1 RentAvg(1),RentAvg(2),RentAvg(3),RentAvg(2)/RentAvg(3)
!average(price per square foot) / average(rent per square foot)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'P/Rent Avg  ',PriceAvg(1)/RentAvg(1),
     1 PriceAvg(2)/RentAvg(2),PriceAvg(3)/RentAvg(3),
     1 (PriceAvg(2)/RentAvg(2))/(PriceAvg(3)/RentAvg(3))
!average(price per unit) / average(labor income workers)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'P*H/Inc Avg ',PriceAvg(1)*Havg(1)/WageAvg(1),
     1 PriceAvg(2)*Havg(2)/WageAvg(2),PriceAvg(3)*Havg(3)/WageAvg(3),
     1 (PriceAvg(2)*Havg(2)/WageAvg(2))/(PriceAvg(3)*Havg(3)/WageAvg(3))
!average(rent per unit) / average(labor income workers)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'R*H/Inc Avg ',RentAvg(1)*Havg(1)/WageAvg(1),
     1 RentAvg(2)*Havg(2)/WageAvg(2),RentAvg(3)*Havg(3)/WageAvg(3),
     1 (RentAvg(2)*Havg(2)/WageAvg(2))/(RentAvg(3)*Havg(3)/WageAvg(3))
!average(net worth workers and retirees)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'NW Avg      ',
     1 NWavg(1),NWavg(2),NWavg(3),NWavg(2)/NWavg(3)
!average(labor income workers)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'Inc Avg     ',
     1 WageAvg(1),WageAvg(2),WageAvg(3),WageAvg(2)/WageAvg(3)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'Hours Avg   ',
     1 HoursAvg(1),HoursAvg(2),HoursAvg(3),HoursAvg(2)/HoursAvg(3)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'H Avg       ',
     1 Havg(1),Havg(2),Havg(3),Havg(2)/Havg(3)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'Hrent Avg   ',
     1 HrentAvg(1),HrentAvg(2),HrentAvg(3),HrentAvg(2)/HrentAvg(3)
      write(6,'(a,f8.4,f8.4,f8.4,f8.4)')
     1 'HRC Avg     ',
     1 HRCavg(1),HRCavg(2),HRCavg(3),HRCavg(2)/HRCavg(3)

!housing supply elasticity
      tempR1=Htot(1)/(HBARloc1(1)+HBARloc2(1))
      tempR2=(Htot(2)*RTSH0loc1+Htot(3)*RTSH0loc2)/Htot(1)
      tempR3=0.25 !0.0 !dw/dh
      tempR4=tempR2*(1.0-tempR1)/
     1      (1.0-tempR2+tempR2*tempR1+tempR2*(1.0-tempR1)*tempR3)
!avg depreciation housing stock
      deprHAvg=deprH(1)*Htot(2)/Htot(1)+deprH(2)*Htot(3)/Htot(1)

!LIHTC subsidy to construction firms
!taxable income, Htot, GovSurplus, are per agent -> Subs, RCshareSubs, should be per agent
      tempR1=(countAllRent(2)*HrentAvg(2)+countAllRC(2)*HRCavg(2))/
     1       (countAll(2)*Havg(2))        !fraction of square feet devoted to renters+RC
      tempR2=(countAllRent(3)*HrentAvg(3)+countAllRC(3)*HRCavg(3))/
     1       (countAll(3)*Havg(3))        !fraction of square feet devoted to renters+RC
      Subs(2)=PriceMkt(2)*tempR1*
     1 RCshare(1,1)*(1-RCrentred(1,1))*RCsubs(1,1)*Htot(2)*deprH(1)
      Subs(3)=PriceMkt(3)*tempR2*
     1 RCshare(2,1)*(1-RCrentred(2,1))*RCsubs(2,1)*Htot(3)*deprH(2)
      Subs(1)=Subs(2)+Subs(3)
      RCShareSubs=Subs(1)/
     1 (WageBill1*tempR1*RCshare(1,1)+WageBill2*tempR2*RCshare(2,1))

      write(6,'(a)')
     1'     pop1   pop2   Own1   Own2  RC1/A1 RC2/A2 RC1/R1 RC2/R2
     1    SRC    Ret1 Ret2   NW/Inc  gNW  gNWwrk  gINC Beq/NW
     1 ElHsup MedInc deprHAvg'
      write(6,'(a,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,
     1 f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3)')
     1 '%% ',countAll(2)/countAll(1),countAll(3)/countAll(1),
     1 1.0-(countAllRent(2)+countAllRC(2))/countAll(2),
     1 1.0-(countAllRent(3)+countAllRC(3))/countAll(3),
     1 countAllRC(2)/countAll(2),
     1 countAllRC(3)/countAll(3),
     1 countAllRC(2)/(countAllRent(2)+countAllRC(2)),
     1 countAllRC(3)/(countAllRent(3)+countAllRC(3)),
     1 fracSameRC,
     1 1.0-countWork(2)/countAll(2),
     1 1.0-countWork(3)/countAll(3),
     1 NWworkavg(1)/WageAvg(1),GiniNW,GiniNWwork,GiniLIwork,
     1 BeqAvg*(NumBorn/real(nAgent))/NWavg(1),tempR4,MedIncomeWorker,
     1 deprHavg
      write(6,'(a)')
     1 '%   SubsLIHTC  RCShareSubs TaxInc  GovSurp  GovSurp/Inc FracSubs
     1    MargRate  Voucher'
      write(6,'(f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4)')
     1 Subs(1),RCShareSubs,TaxableIncomeAvg,HSVgovSurplus,
     1 HSVgovSurplus/TaxableIncomeAvg,HSVfracPay,HSVmargRate,
     1 VoucherExpenseTot

      write(6,'(a,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4)')
     1 'PropTaxIncome ',PropTaxIncomeAvg(1)/countHF(1),
     1 PropTaxIncomeAvg(2)/countHF(2),
     1 HouseValueAvg(1)/countHF(1),
     1 HouseValueAvg(2)/countHF(2),
     1 HouseValueForeignAvg(1)/countHF(1),
     1 HouseValueForeignAvg(2)/countHF(2)

      tempR1=0
      tempR2=0
      tempR3=0
      tempR4=0
      tempR5=0
      tempR6=0
      tempR7=0
      do t=101,TotYears
       tempR1=tempR1+abs(outputErr(t,1))
       tempR2=tempR2+abs(outputErr(t,2))
       tempR3=tempR3+abs(outputErr(t,3))
       tempR4=tempR4+abs(outputErr(t,4))
       tempR5=tempR5+abs(outputErr(t,5))
       tempR6=tempR6+abs(outputErr(t,6))
       tempR7=tempR7+abs(outputErr(t,7))
      end do
      write(6,'(a,f12.5,f12.5,f12.5,f12.5,f12.5,f12.5,f12.5)')
     1 '%err% ',tempR1/real(TotYears-100),tempR2/real(TotYears-100),
     1 tempR3/real(TotYears-100),tempR4/real(TotYears-100),
     1 tempR5/real(TotYears-100),tempR6/real(TotYears-100),
     1 tempR7/real(TotYears-100)

      end

!--------------------------------------------------------------
!This computes some moments from the simulated data
      SUBROUTINE computemoments(TotYears,nAgent,nLOC,nDZ,nAge,nRet,nHF,
     1 DZgrid,SSIdist,AgeProd,RCrentRed,taxss,PriceBond,deprH,taxprop,
     1 taxpropOOT,NumBorn,output,outputWelf,outputErr,
     1 popShare1,rentDiff,incDiff,Rent,Hres,AvgHomeRenter,AvgIncome,
     1 AvgIncomeWorker,MedIncomeWorker,RCshare,RCshareRent,
     1 fracRet,HFgrid0,HFgrid1)
      implicit none
      integer TotYears,nAgent,nLOC,nAge,nRet,t,i,j,iDZ,nDZ,nHF,tempI1
      real output(TotYears,50),outputWelf(TotYears*nAgent,15)
      real outputErr(TotYears,7)
      real Rent(nLOC),PH(nLOC),Hres(nLOC),HresRC(nLOC),HresRenter(nLOC)
      real nLOCall(nLOC),nLOCrent(nLOC),nLOCrc(nLOC),nLOCretmkt(nLOC)
      real LIavg(nLOC),LIMKTavg(nLOC),Pension,Wage,LaborIncome
      real RCrentRed(nLOC,nHF)
      real PHmult(nLOC),NWavg(nLOC),CIavg(nLOC),taxss
      real tempR1,tempR2,tempR3,tempR4,tempR5,tempR6,tempR7,tempR8
      real DZgrid(nAge,nDZ),SSIdist(nDZ),AgeProd(nAge)
      real taxprop(nHF,nLOC),deprH(nLOC),RCshare(nLOC,nHF)
      real popShare1,rentDiff,AvgHomeRenter(nLOC),AvgIncome,Bpos,Bneg
      real AvgIncomeWorker,MedIncomeWorker,RentToIncome
      real RCshareRent(nLOC,nHF),RCavgRent(nLOC,nHF),CapIncome,PriceBond
      real nLOCret(nLOC),fracRet(nLOC),taxpropOOT(nLOC)
      real GiniNWworker,GiniNWall,HFgrid0(nHF,nLOC),HFgrid1(nHF,nLOC)
      real LIavgAll,LIavgWorker,NWavgAll,NWavgWorker
      real NWallSample(10000,1),NWworkerSample(10000,1)
      real LIworkerSample(10000,1)
      integer countall,countworker,sortIndex(10000,1),iHF
      integer countworker1
      real AvgBeq,NumBorn,incDiff,ForDemTot(nLOC)
      real PropTaxIncomeAvg(nHF),countHF(nHF)
      real HouseValueAvg(nHF),HouseValueForeignAvg(nHF)

      do iHF=1,nHF
       PropTaxIncomeAvg(iHF)=0
       HouseValueAvg(iHF)=0
       HouseValueForeignAvg(iHF)=0
       countHF(iHF)=0
      end do
      AvgBeq=0
      LIavgAll=0
      LIavgWorker=0
      NWavgAll=0
      NWavgWorker=0
      countall=0
      countworker=0
      do i=1,nLOC
       do iHF=1,nHF
        RCavgrent(i,iHF)=1.0-RCshare(i,iHF)+
     1                   RCshare(i,iHF)*(1.0-RCrentred(i,iHF))
       end do
       Rent(i)=0
       PH(i)=0
       Hres(i)=0
       HresRC(i)=0
       HresRenter(i)=0
       nLOCall(i)=0
       nLOCrent(i)=0
       nLOCrc(i)=0
       nLOCretmkt(i)=0
       nLOCret(i)=0
       NWavg(i)=0
       LIavg(i)=0
       CIavg(i)=0
       LIMKTavg(i)=0
      end do
      tempR1=0
      tempR2=0
      tempR3=0
      tempR4=0

      countworker1=0
      do t=101,TotYears
       AvgBeq=AvgBeq+output(t,9)
       Rent(1)=Rent(1)+output(t,3)
       Rent(2)=Rent(2)+output(t,4)
       HresRC(1)=HresRC(1)+output(t,22)  !HresRC1
       HresRC(2)=HresRC(2)+output(t,23)  !HresRC2
       HresRenter(1)=HresRenter(1)+output(t,16)  !HresRenter1
       HresRenter(2)=HresRenter(2)+output(t,18)  !HresRenter2
       Hres(1)=Hres(1)+output(t,14)
       Hres(2)=Hres(2)+output(t,15)
       PH(1)=PH(1)+output(t,10) !price1
       PH(2)=PH(2)+output(t,11) !price2
       Pension=output(t,20)
       Wage=output(t,2)
       iHF=nint(output(t,1))
       countHF(iHF)=countHF(iHF)+1.0
       PropTaxIncomeAvg(iHF)=PropTaxIncomeAvg(iHF)+output(t,29)
       HouseValueAvg(iHF)=HouseValueAvg(iHF)+
     1  (output(t,14)*output(t,10)+output(t,15)*output(t,11))
       HouseValueForeignAvg(iHF)=HouseValueForeignAvg(iHF)+
     1  output(t,10)*
     1  exp(HFgrid0(iHF,1)-HFgrid1(iHF,1)*
     1      log(output(t,10)*(1.0+taxpropOOT(1))))+
     1  output(t,11)*
     1  exp(HFgrid0(iHF,2)-HFgrid1(iHF,2)*
     1      log(output(t,11)*(1.0+taxpropOOT(2))))

       do i=1,nAgent
        j=(t-1)*nAgent+i
!        iDZ=1
!        do tempI1=1,nDZ-1
!         if(outputWelf(j,11).gt.DZgrid(nint(outputWelf(j,3)),tempI1)+0.05) iDZ=tempI1+1
!        end do
        iDZ=nint(outputWelf(j,14))

        ForDemTot(1)=exp(HFgrid0(nint(output(t,1)),1)-
     1                   HFgrid1(nint(output(t,1)),1)*
     1                   log(output(t,10)*(1.0+taxpropOOT(1))))    !Foreign Demand per Household in Z1
        ForDemTot(2)=exp(HFgrid0(nint(output(t,1)),2)-
     1                   HFgrid1(nint(output(t,1)),2)*
     1                   log(output(t,11)*(1.0+taxpropOOT(2))))    !Foreign Demand per Household in Z2

        if(nint(outputWelf(j,3)).gt.nAge-nRet) then
         LaborIncome=SSIdist(iDZ)*Pension
         LIavgAll=LIavgAll+LaborIncome
         NWavgAll=NWavgAll+outputWelf(j,13)
        else
!         LaborIncome=outputWelf(j,10)*Wage*(1.0-taxss)*
!     1               outputWelf(j,11)*AgeProd(nint(outputWelf(j,3)))
         LaborIncome=outputWelf(j,10)*Wage*
     1               outputWelf(j,11)*AgeProd(nint(outputWelf(j,3)))
         LIavgAll=LIavgAll+LaborIncome
         LIavgWorker=LIavgWorker+LaborIncome
         NWavgAll=NWavgAll+outputWelf(j,13)
         NWavgWorker=NWavgWorker+outputWelf(j,13)
         countworker=countworker+1
         if(countworker.le.10000) then
          NWworkerSample(countworker,1)=outputWelf(j,13)
         end if
         if(countworker1.lt.10000.and.mod((t-1)*nAgent+i,17).eq.0) then
          countworker1=countworker1+1
          LIworkerSample(countworker1,1)=LaborIncome
         end if
        end if
        countall=countall+1
        if(countall.le.10000) NWallSample(countall,1)=outputWelf(j,13)

        tempI1=nint(outputWelf(j,5)) !zone
        Bpos=outputWelf(j,6)
        if(Bpos.lt.0) Bpos=0
        Bneg=outputWelf(j,6)
        if(Bneg.gt.0) Bneg=0
        CapIncome=Bpos*(1.0-PriceBond)+
     1    outputWelf(j,7)*RCavgRent(tempI1,iHF)*
     1   (Rent(tempI1)-PH(tempI1)*(deprH(tempI1)+taxprop(iHF,tempI1)))+
     1    Bneg*(1.0-PriceBond)*
     1    outputWelf(j,7)/(outputWelf(j,7)+outputWelf(j,9))
        if(abs(outputWelf(j,5)-1.0).lt..01) then
         nLOCall(1)=nLOCall(1)+1.0                !living in Z1
         if(abs(outputWelf(j,12)-2.0).gt..01)nLOCrent(1)=nLOCrent(1)+1.0  !renting in Z1
         if(abs(outputWelf(j,12)-3.0).lt..01) nLOCrc(1)=nLOCrc(1)+1.0  !rent controlled in Z1
         if(outputWelf(j,3).gt.real(nAge-nRet)+0.01)
     1      nLOCret(1)=nLOCret(1)+1.0
         if(outputWelf(j,3).gt.real(nAge-nRet)+0.01.and.
     1      abs(outputWelf(j,12)-3.0).gt..01)
     1      nLOCretmkt(1)=nLOCretmkt(1)+1.0
         NWavg(1)=NWavg(1)+outputWelf(j,13) !NW
         LIavg(1)=LIavg(1)+LaborIncome      !income
         if(abs(outputWelf(j,12)-3.0).gt..01)
     1      LIMKTavg(1)=LIMKTavg(1)+LaborIncome
         CIavg(1)=CIavg(1)+CapIncome      !income
         if(abs(outputWelf(j,12)-3.0).lt..01) then
          tempR1=tempR1+
     1 output(t,10)*outputWelf(j,9)*(1.0-RCrentred(1,iHF))
         else
          tempR1=tempR1+output(t,10)*outputWelf(j,9)
          tempR3=tempR3+output(t,10)*outputWelf(j,9)
         end if
         tempR1=tempR1+output(t,10)*ForDemTot(1)
         tempR3=tempR3+output(t,10)*ForDemTot(1)
        end if
        if(abs(outputWelf(j,5)-2.0).lt..01) then
         nLOCall(2)=nLOCall(2)+1.0                !living in Z1
         if(abs(outputWelf(j,12)-2.0).gt..01)nLOCrent(2)=nLOCrent(2)+1.0  !renting in Z2
         if(abs(outputWelf(j,12)-3.0).lt..01) nLOCrc(2)=nLOCrc(2)+1.0  !rent controlled in Z2
         if(outputWelf(j,3).gt.real(nAge-nRet)+0.01)
     1      nLOCret(2)=nLOCret(2)+1.0
         if(outputWelf(j,3).gt.real(nAge-nRet)+0.01.and.
     1      abs(outputWelf(j,12)-3.0).gt..01)
     1      nLOCretmkt(2)=nLOCretmkt(2)+1.0
         NWavg(2)=NWavg(2)+outputWelf(j,13) !NW
         LIavg(2)=LIavg(2)+LaborIncome      !income
         if(abs(outputWelf(j,12)-3.0).gt..01)
     1      LIMKTavg(2)=LIMKTavg(2)+LaborIncome

         CIavg(2)=CIavg(2)+CapIncome
         if(abs(outputWelf(j,12)-3.0).lt..01) then
          tempR2=tempR2+
     1 output(t,11)*outputWelf(j,9)*(1.0-RCrentred(2,iHF))
         else
          tempR2=tempR2+output(t,11)*outputWelf(j,9)
          tempR4=tempR4+output(t,11)*outputWelf(j,9)
         end if
         tempR2=tempR2+output(t,11)*ForDemTot(2)
         tempR4=tempR4+output(t,11)*ForDemTot(2)
        end if
       end do
      end do

      do i=1,nLOC
       Rent(i)=Rent(i)/real(TotYears-100)
       PH(i)=PH(i)/real(TotYears-100)
       Hres(i)=Hres(i)/real(TotYears-100)
       HresRC(i)=HresRC(i)/real(TotYears-100)
       HresRenter(i)=HresRenter(i)/real(TotYears-100)
       nLOCall(i)=nLOCall(i)/real(TotYears-100)
       nLOCrent(i)=nLOCrent(i)/real(TotYears-100)
       nLOCrc(i)=nLOCrc(i)/real(TotYears-100)
       nLOCretmkt(i)=nLOCretmkt(i)/real(TotYears-100)
       nLOCret(i)=nLOCret(i)/real(TotYears-100)
       PHmult(i)=1.0-(HresRC(i)/Hres(i))+
     1      (HresRC(i)/Hres(i))*(1.0-RCrentred(i,1))   !average rent (or price) in zone as fraction of market rent (or price)
       LIavg(i)=LIavg(i)/(real(TotYears-100)*nLOCall(i))
       CIavg(i)=CIavg(i)/(real(TotYears-100)*nLOCall(i))
       NWavg(i)=NWavg(i)/(real(TotYears-100)*nLOCall(i))
       LIMKTavg(i)=LIMKTavg(i)/
     1            (real(TotYears-100)*(nLOCall(i)-nLOCrc(i)))
      end do


      call sort(NWallSample,10000,SortIndex)
      tempR5=0
      tempR6=0
      do i=1,10000
       tempR5=tempR5+real(i)*NWallSample(i,1)
       tempR6=tempR6+NWallSample(i,1)
      end do
      GiniNWall=((2.0*tempR5)/(10000.0*tempR6))-1.0
      call sort(NWworkerSample,10000,SortIndex)
      tempR5=0
      tempR6=0
      do i=1,10000
       tempR5=tempR5+real(i)*NWworkerSample(i,1)
       tempR6=tempR6+NWworkerSample(i,1)
      end do
      GiniNWworker=((2.0*tempR5)/(10000.0*tempR6))-1.0

      AvgBeq=AvgBeq/real(TotYears-100)
      tempR1=tempR1/real(TotYears-100)  !sum(PH1*Hres1) = price of all housing in Z1
      tempR2=tempR2/real(TotYears-100)  !sum(PH2*Hres2) = price of all housing in Z2
      tempR3=tempR3/real(TotYears-100)  !sum(PH1*Hres1|mkt) = price of all housing in Z1
      tempR4=tempR4/real(TotYears-100)  !sum(PH2*Hres2|mkt)= price of all housing in Z2

      tempR5=tempR1/(Hres(1)*real(nAgent))  !mean(P1) which already accounts for lower price in rent controlled
      tempR6=tempR2/(Hres(2)*real(nAgent))  !mean(P2) which already accounts for lower price in rent controlled
      tempR7=tempR3/((Hres(1)-HresRC(1))*real(nAgent)) !mean(P1|mkt)
      tempR8=tempR4/((Hres(2)-HresRC(2))*real(nAgent)) !mean(P2|mkt)

      write(6,*) '               Z1      Z2    Z1/Z2'
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Mkt Rent    ',Rent(1),Rent(2),Rent(1)/Rent(2)
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg Rent    ',Rent(1)*(tempR5/tempR7),Rent(2)*(tempR6/tempR8),
     1 (Rent(1)*(tempR5/tempR7))/(Rent(2)*(tempR6/tempR8))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg P/Rent  ',PH(1)/Rent(1),PH(2)/Rent(2),
     1  (PH(1)/Rent(1))/(PH(2)/Rent(2))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Mkt P/LabInc',tempR3/(LIMKTavg(1)*(nLOCall(1)-nLOCrc(1))),
     1 tempR4/(LIMKTavg(2)*(nLOCall(2)-nLOCrc(2))),
     1 (tempR3/(LIMKTavg(1)*(nLOCall(1)-nLOCrc(1))))/
     1 (tempR4/(LIMKTavg(2)*(nLOCall(2)-nLOCrc(2))))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg P/LabInc',tempR1/(LIavg(1)*nLOCall(1)),
     1 tempR2/(LIavg(2)*nLOCall(2)),
     1 (tempR1/(LIavg(1)*nLOCall(1)))/(tempR2/(LIavg(2)*nLOCall(2)))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg P/TotInc',tempR1/((LIavg(1)+CIavg(1))*nLOCall(1)),
     1 tempR2/((LIavg(2)+CIavg(2))*nLOCall(2)),
     1 (tempR1/((LIavg(1)+CIavg(1))*nLOCall(1)))/
     1 (tempR2/((LIavg(2)+CIavg(2))*nLOCall(2)))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg NetWorth',NWavg(1),NWavg(2),NWavg(1)/NWavg(2)
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg LabInc  ',LIavg(1),LIavg(2),LIavg(1)/LIavg(2)
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg TotInc  ',LIavg(1)+CIavg(1),LIavg(2)+CIavg(2),
     1 (LIavg(1)+CIavg(1))/(LIavg(2)+CIavg(2))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg IncMkt  ',LIMKTavg(1),LIMKTavg(2),LIMKTavg(1)/LIMKTavg(2)
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg Home    ',Hres(1)*real(nAgent)/nLOCall(1),
     1  Hres(2)*real(nAgent)/nLOCall(2),
     1 (Hres(1)/nLOCall(1))/(Hres(2)/nLOCall(2))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg HomeRent',
     1 (HresRenter(1)-HresRC(1))*real(nAgent)/(nLOCrent(1)-nLOCrc(1)),
     1 (HresRenter(2)-HresRC(2))*real(nAgent)/(nLOCrent(2)-nLOCrc(2)),
     1 ((HresRenter(1)-HresRC(1))*real(nAgent)/(nLOCrent(1)-nLOCrc(1)))/
     1 ((HresRenter(2)-HresRC(2))*real(nAgent)/(nLOCrent(2)-nLOCrc(2)))
      write(6,'(a,f8.4,f8.4,f8.4)')
     1 'Avg HomeRC  ',HresRC(1)*real(nAgent)/nLOCrc(1),
     1 HresRC(2)*real(nAgent)/nLOCrc(2),
     1 (HresRC(1)/nLOCrc(1))/(HresRC(2)/nLOCrc(2))
      fracRet(1)=nLOCret(1)/nLOCall(1)
      fracRet(2)=nLOCret(2)/nLOCall(2)
      write(6,'(a)')
     1'     pop1   pop2   Own1   Own2  RC1/A1 RC2/A2 RC1/R1 RC2/R2  Ret1
     1m  Ret2m  Ret1   Ret2'
      write(6,'(a,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,
     1 f7.3,f7.3,f7.3,f7.3,f7.3,f7.3,f7.3)')
     1 '%% ',nLOCall(1)/(nLOCall(1)+nLOCall(2)),
     1 nLOCall(2)/(nLOCall(1)+nLOCall(2)),
     1     1.0-(nLOCrent(1)/nLOCall(1)),
     1     1.0-(nLOCrent(2)/nLOCall(2)),
     1 nLOCrc(1)/nLOCall(1),nLOCrc(2)/nLOCall(2),
     1 nLOCrc(1)/nLOCrent(1),nLOCrc(2)/nLOCrent(2),
     1 nLOCretmkt(1)/nLOCall(1),nLOCretmkt(2)/nLOCall(2),
     1 nLOCret(1)/nLOCall(1),nLOCret(2)/nLOCall(2),
     1 NWavgAll/LIavgAll,NWavgWorker/LIavgWorker,GiniNWall,GiniNWworker,
     1 AvgBeq*NumBorn/(NWavgAll/real(TotYears-100))
      write(6,'(a,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4)')
     1 'PropTaxIncome ',PropTaxIncomeAvg(1)/countHF(1),
     1 PropTaxIncomeAvg(2)/countHF(2),
     1 HouseValueAvg(1)/countHF(1),HouseValueAvg(2)/countHF(2),
     1 HouseValueForeignAvg(1)/countHF(1),
     1 HouseValueForeignAvg(2)/countHF(2)

      popShare1=nLOCall(1)/(nLOCall(1)+nLOCall(2))
      rentDiff=Rent(1)/Rent(2)
      AvgHomeRenter(1)=(HresRenter(1)-HresRC(1))*real(nAgent)/
     1                 (nLOCrent(1)-nLOCrc(1))
      AvgHomeRenter(2)=(HresRenter(2)-HresRC(2))*real(nAgent)/
     1                 (nLOCrent(2)-nLOCrc(2))
      AvgIncome=LIavgAll/real(countall)!popShare1*LIavg(1)+(1.0-popShare1)*LIavg(2)
      AvgIncomeWorker=LIavgWorker/real(countworker)
      call sort(LIworkerSample,10000,SortIndex)
      MedIncomeWorker=LIworkerSample(5000,1)

      do iHF=1,nHF
       RCshareRent(1,iHF)=nLOCrc(1)/nLOCrent(1)
       RCshareRent(2,iHF)=nLOCrc(2)/nLOCrent(2)
      end do
      incDiff=LIavg(1)/LIavg(2)
      RentToIncome=
     1 (Hres(1)*Rent(1)*RCavgrent(1,1)+Hres(2)*Rent(2)*RCavgrent(2,1))/
     1  AvgIncomeWorker

      tempR1=0
      tempR2=0
      tempR3=0
      tempR4=0
      tempR5=0
      tempR6=0
      tempR7=0
      do t=101,TotYears
       tempR1=tempR1+abs(outputErr(t,1))
       tempR2=tempR2+abs(outputErr(t,2))
       tempR3=tempR3+abs(outputErr(t,3))
       tempR4=tempR4+abs(outputErr(t,4))
       tempR5=tempR5+abs(outputErr(t,5))
       tempR6=tempR6+abs(outputErr(t,6))
       tempR7=tempR7+abs(outputErr(t,7))
      end do
      write(6,'(a,f12.5,f12.5,f12.5,f12.5,f12.5,f12.5,f12.5)')
     1 '%err% ',tempR1/real(TotYears-100),tempR2/real(TotYears-100),
     1 tempR3/real(TotYears-100),tempR4/real(TotYears-100),
     1 tempR5/real(TotYears-100),tempR6/real(TotYears-100),
     1 tempR7/real(TotYears-100)

      end
!--------------------------------------------------------------
!This writes an ngrid by nwidth matrix to the file 'filename'
      SUBROUTINE writedatabinary(arrout,filename,nlength,nwidth)
      implicit none
      integer nlength,nwidth,iunit
      character(len=9) filename
      real arrout(nlength,nwidth)
      data iunit /11/

      open(unit=iunit,file=filename,status='old',form='UNFORMATTED')
      write(iunit) arrout
      close(iunit)

      end

!--------------------------------------------------------------
!This writes an ngrid by nwidth matrix to the file 'filename'
      SUBROUTINE readdatabinary(arrout,filename,nlength,nwidth)
       implicit none
       integer nlength,nwidth,iunit
       character(len=9) filename
       real arrout(nlength,nwidth)
       data iunit /11/

       open(unit=iunit,file=filename,status='old',form='UNFORMATTED')
       read(iunit) arrout
       close(iunit)

       end

!--------------------------------------------------------------
!This writes an ngrid by nwidth matrix to the file 'filename'
      SUBROUTINE writedata(arrout,filename,nlength,nwidth,mlength,
     1 mwidth)
      implicit none
      integer nlength,nwidth,iunit,i,j,mlength,mwidth
      character(len=10) filename
      real arrout(mlength,mwidth)
      data iunit /11/

      open(unit=iunit,file=filename,status='old',form='FORMATTED')

      do i=1,nlength
       write(iunit,*) (arrout(i,j), j=1,nwidth)
      end do

      close(iunit)

      return
      end

!--------------------------------------------------------------
!This writes an ngrid by nwidth matrix to the file 'filename'
      SUBROUTINE writedataNW(arrout,filename,nlength,nwidth,mlength,
     1 mwidth)
      implicit none
      integer nlength,nwidth,iunit,i,j,mlength,mwidth
      character(len=10) filename
      real arrout(mlength,mwidth)
      data iunit /11/

      open(unit=iunit,file=filename,status='old',form='FORMATTED')

      do i=1,nlength
       write(iunit,'(
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,
     1 f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5,f11.5)')
     1 (arrout(i,j),j=1,nwidth)
      end do

      close(iunit)

      return
      end

!--------------------------------------------------------------
!This writes an ngrid by nwidth matrix to the file 'filename'
      SUBROUTINE writedata1(arrout,filename,nlength,nwidth,mlength,
     1 mwidth,
     1 nHF,nDZ,nLOC,nAge,nRet,HFgrid0,HFgrid1,HFVgrid,DZgrid,SSIdist,
     1 RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,PriceBond,
     1 taxss,taxprop,taxpropOOT,gamma0,alphaC,alphaH,alphaN,
     1 ElastCH,ElastCN,chi0,HoursMin,deprH,deprINV0,
     1 TrProbDZ,tau0,lambda0,tauBase,lambdaBase,
     1 CommCost,CommCostFin,beta0,BetaRel,
     1 Z1shiftCut,Z1shiftAll,Z1shiftSize,thetaRes,thetaInv,
     1 HresMin,RCshare,RCrentred,RCinccut,RChsize,RCprobStay,kappa2,
     1 kappa3,RCsubs,ProfitRedist)
      implicit none
      integer nlength,nwidth,iunit,i,j,mlength,mwidth
      character(len=10) filename
      real arrout(mlength,mwidth)
      integer nHF,nLOC,nAge,nRet,nDZ
      real HFgrid0(nHF,nLOC),HFgrid1(nHF,nLOC),HFVgrid(nHF,nLOC)
      real DZgrid(nAge,nDZ),SSIdist(nDZ)
      real RTSC,RTSH0loc1,HBARloc1(nHF),RTSH0loc2,HBARloc2(nHF)
      real taxpropOOT(nLOC),RCsubs(nLOC,nHF)
      real PriceBond,taxss,taxprop(nHF,nLOC)
      real gamma0,alphaC,alphaH,alphaN
      real deprINV0,deprH(nLOC),ElastCH,ElastCN,chi0,HoursMin
      real TrProbDZ(nDZ,nDZ),tau0(nHF),lambda0(nHF),tauBase,lambdaBase
      real CommCost(nLOC,2),ProfitRedist(3)
      real CommCostFin(nLOC,2),beta0,BetaRel(nDZ),Z1shiftCut(2)
      real Z1shiftAll,Z1shiftSize(2),thetaRes,thetaInv,HresMin
      real RCshare(nLOC,nHF),RCrentred(nLOC,nHF),RCinccut(nLOC,nHF)
      real RChsize(nLOC,nHF),RCprobStay(nLOC),kappa2,kappa3

      write(6,*) 'inside'
      write(6,*) RCshare(1,1),RCshare(2,1),RCshare(1,2),RCshare(2,2)
      write(6,*) RCrentred(1,1),RCrentred(2,1),RCrentred(1,2),
     1 RCrentred(2,2)
      write(6,*) RCinccut(1,1),RCinccut(2,1),RCinccut(1,2),RCinccut(2,2)
      write(6,*) RChsize(1,1),RChsize(2,1),RChsize(1,2),RChsize(2,2)
      write(6,*) RCprobStay(1),RCprobStay(2),kappa2,kappa3,HresMin
      
      data iunit /11/

      open(unit=iunit,file=filename,status='old',form='FORMATTED')

      write(iunit,*) 'nRet=',nRet,';'
      write(iunit,*) 'HFgrid0=[',(HFgrid0(1,i),i=1,nLOC),';',
     1                           (HFgrid0(2,i),i=1,nLOC),'];'
      write(iunit,*) 'HFgrid1=[',(HFgrid1(1,i),i=1,nLOC),';',
     1                           (HFgrid1(2,i),i=1,nLOC),'];'
      write(iunit,*) 'HFVgrid=[',(HFVgrid(1,i),i=1,nLOC),';',
     1                           (HFVgrid(2,i),i=1,nLOC),'];'
      write(iunit,*) 'RTSC=',RTSC,'; RTSH0loc1=',RTSH0loc1,
     1 ';HBARloc1=[',(HBARloc1(i),i=1,nHF),'];'
      write(iunit,*) 'RTSH0loc2=',RTSH0loc2,';HBARloc2=[',
     1 (HBARloc2(i),i=1,nHF),'];'
      write(iunit,*) 'PriceBond=',PriceBond,';taxss=',taxss,';gamma0=',
     1 gamma0,';'
      write(iunit,*) 'taxprop(1,1)=',taxprop(1,1),';taxprop(2,1)=',
     1 taxprop(2,1),';'
      write(iunit,*) 'taxprop(1,2)=',taxprop(1,2),';taxprop(2,2)=',
     1 taxprop(2,2),';'
      write(iunit,*) 'taxpropOOT(1)=',taxpropOOT(1),
     1 ';taxpropOOT(2)=',taxpropOOT(2),';'
      write(iunit,*) 'alphaC=',alphaC,';alphaH=',alphaH,
     1 ';alphaN=',alphaN,';'
      write(iunit,*) 'ElastCN=',ElastCN,';ElastCH=',ElastCH,';'
      write(iunit,*) 'chi0=',chi0,';HoursMin=',HoursMin,';'
      write(iunit,*) 'deprH=[',deprH(1),deprH(2),']; deprINV0=',
     1 deprINV0,';'
      write(iunit,*) 'DZgrid=['
      do j=1,nAge
      write(iunit,'(f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4)')
     1 (DZgrid(j,i),i=1,nDZ)
      end do
      write(iunit,*) '];'
      write(iunit,*) 'SSIdist=['
      write(iunit,'(f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4,f10.4)')
     1  (SSIdist(i),i=1,nDZ)
      write(iunit,*) '];'
      write(iunit,*) 'TrProbDZ11=',TrProbDZ(1,1),';TrProbDZ22=',
     1 TrProbDZ(2,2),';'
      write(iunit,*) 'TrProbDZ33=',TrProbDZ(3,3),';TrProbDZ44=',
     1 TrProbDZ(4,4),';'
      write(iunit,*) 'tau0=[',(tau0(i),i=1,nHF),'];'
      write(iunit,*) 'lambda0=[',(lambda0(i),i=1,nHF),'];'
      write(iunit,*) 'tauBase=',tauBase,';lambdaBase=',lambdaBase,';'
      write(iunit,*) 'CommCost=',CommCost(2,1),';'
      write(iunit,*) 'CommCostFin=',CommCostFin(2,1),';'
      write(iunit,*) 'beta=',beta0,';'
      write(iunit,*) 'BetaRel(1)=',BetaRel(1),
     1 ';BetaRel(2)=',BetaRel(nDZ/2+1),';'
      write(iunit,*) 'Z1shiftCut(1)=',Z1shiftCut(1),
     1 ';Z1shiftCut(2)=',Z1shiftCut(2),';'
      write(iunit,*) 'Z1shiftSize(1)=',Z1shiftSize(1),
     1 ';Z1shiftSize(2)=',Z1shiftSize(2),';'
      write(iunit,*) 'Z1shiftAll=',Z1shiftAll,';thetaRes=',thetaRes,';'
      write(iunit,*) 'thetaInv=',thetaInv,';HresMin=',HresMin,';'
      write(iunit,*) 'kappa2=',kappa2,';kappa3=',kappa3,';'
      write(iunit,*) 'RCprobStay(1)=',RCprobStay(1),
     1 ';RCprobStay(2)=',RCprobStay(2),';'
      write(iunit,*) 'RCshare(1,1)=',RCshare(1,1),';RCshare(2,1)=',
     1 RCshare(2,1),';'
      write(iunit,*) 'RCshare(1,2)=',RCshare(1,2),';RCshare(2,2)=',
     1 RCshare(2,2),';'
      write(iunit,*) 'RCrentred(1,1)=',RCrentred(1,1),';RCrentred(2,1)='
     1 ,RCrentred(2,1),';'
      write(iunit,*) 'RCrentred(1,2)=',RCrentred(1,2),';RCrentred(2,2)='
     1 ,RCrentred(2,2),';'
      write(iunit,*) 'RCinccut(1,1)=',RCinccut(1,1),';RCinccut(2,1)=',
     1 RCinccut(2,1),';'
      write(iunit,*) 'RCinccut(1,2)=',RCinccut(1,2),';RCinccut(2,2)=',
     1 RCinccut(2,2),';'
      write(iunit,*) 'RChsize(1,1)=',RChsize(1,1),';RChsize(2,1)=',
     1 RChsize(2,1),';'
      write(iunit,*) 'RChsize(1,2)=',RChsize(1,2),';RChsize(2,2)=',
     1 RChsize(2,2),';'
      write(iunit,*) 'RCsubs(1,1)=',RCsubs(1,1),';RCsubs(2,1)=',
     1 RCsubs(2,1),';'
      write(iunit,*) 'RCsubs(1,2)=',RCsubs(1,2),';RCsubs(2,2)=',
     1 RCsubs(2,2),';'
      write(iunit,*) 'ProfitRedist=[',(ProfitRedist(i),i=1,3),'];'

      write(iunit,*) 'outInd=['

      do i=1,nlength
       write(iunit,'(f17.4,f17.4,f11.4,f11.4,f11.4,f11.4,
     1 f11.4,f11.4,f11.4,f11.4,f11.4,f11.4,f11.4,f9.2,f9.2)')
     1  (arrout(i,j), j=1,nwidth)
      end do

      write(iunit,*) '];'

      close(iunit)

      return

      end

!----------------------------------------------------------------
!this reads a nlength by nwidth matrix from the file 'filename'
      SUBROUTINE readdata(arrout,filename,nlength,nwidth,mlength,mwidth)
      implicit none
      integer nlength,iunit,nwidth,i,j,mlength,mwidth
      character(len=10) filename
      real readnum(nwidth)
      real arrout(mlength,mwidth)
      data iunit /10/

      open(unit=iunit,file=filename,status='old',form='FORMATTED')

      do i=1,nlength
       read(iunit,*,end=1011) readnum
       do j=1,nwidth
        arrout(i,j)=readnum(j)
       end do
      end do

 1011 continue

      close(iunit)

      return
      end
!------------------------------------------------------------------
      SUBROUTINE writeoutput(arrout,filename,nlength,nwidth,mlength,
     1 mwidth)
      implicit none
      integer nlength,nwidth,iunit,i,j,mlength,mwidth
      integer remainder10,whole10,i10
      character(len=10) filename
      real arrout(mlength,mwidth)
      data iunit /11/

      open(unit=iunit,file=filename,status='old',form='FORMATTED')

      remainder10=mod(nwidth,10)
      whole10=(nwidth-remainder10)/10

      do i10=1,whole10
       if(i10.lt.10) then
        write(iunit,'(a4,i1,a3)') 'temp',i10,'=['
       else
        write(iunit,'(a4,i2,a3)') 'temp',i10,'=['
       end if
       do i=1,nlength
        write(iunit,'(f13.6,f13.6,f13.6,f13.6,f13.6,f13.6,f13.6,f13.6,
     1                f13.6,f13.6)') (arrout(i,(i10-1)*10+j), j=1,10)
       end do
       write(iunit,*) '];'
      end do

      if(remainder10.gt.0) then
       if(whole10+1.lt.10) then
        write(iunit,'(a4,i1,a3)') 'temp',whole10+1,'=['
       else
        write(iunit,'(a4,i2,a3)') 'temp',whole10+1,'=['
       end if
       do i=1,nlength
        write(iunit,'(f13.6,f13.6,f13.6,f13.6,f13.6,f13.6,f13.6,f13.6,
     1    f13.6,f13.6)') (arrout(i,(whole10+1-1)*10+j), j=1,remainder10)
       end do
       write(iunit,*) '];'
      end if

      close(iunit)

      return
      end

!-------------------------------------------------------------------
      SUBROUTINE findspot(Kgrid,nK,Knext,iK,iKnext)
      implicit none
      integer nK,iK,iKnext,i
      real Knext,Kgrid(nK)

      if(Knext.lt.Kgrid(iK)) then
       do i=0,iK-1
        if(Knext.lt.Kgrid(iK-i)) then
         iKnext=iK-i-1
        else
         goto 101
        end if
       end do
 101   continue
       if(iKnext.lt.1) iKnext=1
      else
       if(iK.eq.nK) then
        iKnext=nK-1
        goto 102
       end if
       do i=iK,nK-1
        if(Knext.ge.Kgrid(i)) then
         iKnext=i
        else
         goto 102
        end if
       end do
 102   continue
      end if

      end

!---------------------------------
!This writes an ngrid by nwidth matrix to the file 'filename'
      SUBROUTINE writedata9(arrout,filename,nlength,nwidth,mlength,
     1 mwidth)
       implicit none
       integer nlength,nwidth,iunit,i,j,mlength,mwidth
       character(len=9) filename
       real arrout(mlength,mwidth)
       data iunit /11/

       open(unit=iunit,file=filename,status='old',form='FORMATTED')

       do i=1,nlength
       write(iunit,*) (arrout(i,j), j=1,nwidth)
       end do

       close(iunit)

       return
      end

!----------------------------------------------------------------
!this reads a nlength by nwidth matrix from the file 'filename'
      SUBROUTINE readdata9(arrout,filename,nlength,nwidth,mlength,
     1 mwidth)
       implicit none
       integer nlength,iunit,nwidth,i,j,mlength,mwidth
       character(len=9) filename
       real readnum(nwidth)
       real arrout(mlength,mwidth)
       data iunit /10/

       open(unit=iunit,file=filename,status='old',form='FORMATTED')

       do i=1,nlength
        read(iunit,*,end=1011) readnum
        do j=1,nwidth
         arrout(i,j)=readnum(j)
        end do
       end do
       close(iunit)

 1011  continue

       return
       end

!-------------------------------------
      subroutine getfilenamedat(filename,t,flag,flagBeq)
      implicit none
      character(len=9) filename
      integer t,flag,flagBeq

       if(flagBeq.eq.0) then
       if(flag.eq.1) then
        if(t.eq.1) filename='pol01.dat'
        if(t.eq.2) filename='pol02.dat'
        if(t.eq.3) filename='pol03.dat'
        if(t.eq.4) filename='pol04.dat'
        if(t.eq.5) filename='pol05.dat'
        if(t.eq.6) filename='pol06.dat'
        if(t.eq.7) filename='pol07.dat'
        if(t.eq.8) filename='pol08.dat'
        if(t.eq.9) filename='pol09.dat'
        if(t.eq.10) filename='pol10.dat'
        if(t.eq.11) filename='pol11.dat'
        if(t.eq.12) filename='pol12.dat'
        if(t.eq.13) filename='pol13.dat'
        if(t.eq.14) filename='pol14.dat'
        if(t.eq.15) filename='pol15.dat'
        if(t.eq.16) filename='pol16.dat'
        if(t.eq.17) filename='pol17.dat'
        if(t.eq.18) filename='pol18.dat'
        if(t.eq.19) filename='pol19.dat'
        if(t.eq.20) filename='pol20.dat'
        if(t.eq.21) filename='pol21.dat'
        if(t.eq.22) filename='pol22.dat'
        if(t.eq.23) filename='pol23.dat'
        if(t.eq.24) filename='pol24.dat'
        if(t.eq.25) filename='pol25.dat'
        if(t.eq.26) filename='pol26.dat'
        if(t.eq.27) filename='pol27.dat'
        if(t.eq.28) filename='pol28.dat'
        if(t.eq.29) filename='pol29.dat'
        if(t.eq.30) filename='pol30.dat'
        if(t.eq.31) filename='pol31.dat'
        if(t.eq.32) filename='pol32.dat'
        if(t.eq.33) filename='pol33.dat'
        if(t.eq.34) filename='pol34.dat'
        if(t.eq.35) filename='pol35.dat'
        if(t.eq.36) filename='pol36.dat'
        if(t.eq.37) filename='pol37.dat'
        if(t.eq.38) filename='pol38.dat'
        if(t.eq.39) filename='pol39.dat'
        if(t.eq.40) filename='pol40.dat'
        if(t.eq.41) filename='pol41.dat'
        if(t.eq.42) filename='pol42.dat'
        if(t.eq.43) filename='pol43.dat'
        if(t.eq.44) filename='pol44.dat'
        if(t.eq.45) filename='pol45.dat'
        if(t.eq.46) filename='pol46.dat'
        if(t.eq.47) filename='pol47.dat'
        if(t.eq.48) filename='pol48.dat'
        if(t.eq.49) filename='pol49.dat'
        if(t.eq.50) filename='pol50.dat'
        if(t.eq.51) filename='pol51.dat'
        if(t.eq.52) filename='pol52.dat'
        if(t.eq.53) filename='pol53.dat'
        if(t.eq.54) filename='pol54.dat'
        if(t.eq.55) filename='pol55.dat'
        if(t.eq.56) filename='pol56.dat'
        if(t.eq.57) filename='pol57.dat'
        if(t.eq.58) filename='pol58.dat'
        if(t.eq.59) filename='pol59.dat'
        if(t.eq.60) filename='pol60.dat'
        if(t.eq.61) filename='pol61.dat'
        if(t.eq.62) filename='pol62.dat'
        if(t.eq.63) filename='pol63.dat'
        if(t.eq.64) filename='pol64.dat'
        if(t.eq.65) filename='pol65.dat'
        if(t.eq.66) filename='pol66.dat'
        if(t.eq.67) filename='pol67.dat'
        if(t.eq.68) filename='pol68.dat'
        if(t.eq.69) filename='pol69.dat'
        if(t.eq.70) filename='pol70.dat'
        if(t.eq.71) filename='pol71.dat'
        if(t.eq.72) filename='pol72.dat'
        if(t.eq.73) filename='pol73.dat'
        if(t.eq.74) filename='pol74.dat'
        if(t.eq.75) filename='pol75.dat'
        if(t.eq.76) filename='pol76.dat'
        if(t.eq.77) filename='pol77.dat'
        if(t.eq.78) filename='pol78.dat'
        if(t.eq.79) filename='pol79.dat'
        if(t.eq.80) filename='pol80.dat'
       end if
       if(flag.eq.2) then
        if(t.eq.1) filename='val01.dat'
        if(t.eq.2) filename='val02.dat'
        if(t.eq.3) filename='val03.dat'
        if(t.eq.4) filename='val04.dat'
        if(t.eq.5) filename='val05.dat'
        if(t.eq.6) filename='val06.dat'
        if(t.eq.7) filename='val07.dat'
        if(t.eq.8) filename='val08.dat'
        if(t.eq.9) filename='val09.dat'
        if(t.eq.10) filename='val10.dat'
        if(t.eq.11) filename='val11.dat'
        if(t.eq.12) filename='val12.dat'
        if(t.eq.13) filename='val13.dat'
        if(t.eq.14) filename='val14.dat'
        if(t.eq.15) filename='val15.dat'
        if(t.eq.16) filename='val16.dat'
        if(t.eq.17) filename='val17.dat'
        if(t.eq.18) filename='val18.dat'
        if(t.eq.19) filename='val19.dat'
        if(t.eq.20) filename='val20.dat'
        if(t.eq.21) filename='val21.dat'
        if(t.eq.22) filename='val22.dat'
        if(t.eq.23) filename='val23.dat'
        if(t.eq.24) filename='val24.dat'
        if(t.eq.25) filename='val25.dat'
        if(t.eq.26) filename='val26.dat'
        if(t.eq.27) filename='val27.dat'
        if(t.eq.28) filename='val28.dat'
        if(t.eq.29) filename='val29.dat'
        if(t.eq.30) filename='val30.dat'
        if(t.eq.31) filename='val31.dat'
        if(t.eq.32) filename='val32.dat'
        if(t.eq.33) filename='val33.dat'
        if(t.eq.34) filename='val34.dat'
        if(t.eq.35) filename='val35.dat'
        if(t.eq.36) filename='val36.dat'
        if(t.eq.37) filename='val37.dat'
        if(t.eq.38) filename='val38.dat'
        if(t.eq.39) filename='val39.dat'
        if(t.eq.40) filename='val40.dat'
        if(t.eq.41) filename='val41.dat'
        if(t.eq.42) filename='val42.dat'
        if(t.eq.43) filename='val43.dat'
        if(t.eq.44) filename='val44.dat'
        if(t.eq.45) filename='val45.dat'
        if(t.eq.46) filename='val46.dat'
        if(t.eq.47) filename='val47.dat'
        if(t.eq.48) filename='val48.dat'
        if(t.eq.49) filename='val49.dat'
        if(t.eq.50) filename='val50.dat'
        if(t.eq.51) filename='val51.dat'
        if(t.eq.52) filename='val52.dat'
        if(t.eq.53) filename='val53.dat'
        if(t.eq.54) filename='val54.dat'
        if(t.eq.55) filename='val55.dat'
        if(t.eq.56) filename='val56.dat'
        if(t.eq.57) filename='val57.dat'
        if(t.eq.58) filename='val58.dat'
        if(t.eq.59) filename='val59.dat'
        if(t.eq.60) filename='val60.dat'
        if(t.eq.61) filename='val61.dat'
        if(t.eq.62) filename='val62.dat'
        if(t.eq.63) filename='val63.dat'
        if(t.eq.64) filename='val64.dat'
        if(t.eq.65) filename='val65.dat'
        if(t.eq.66) filename='val66.dat'
        if(t.eq.67) filename='val67.dat'
        if(t.eq.68) filename='val68.dat'
        if(t.eq.69) filename='val69.dat'
        if(t.eq.70) filename='val70.dat'
        if(t.eq.71) filename='val71.dat'
        if(t.eq.72) filename='val72.dat'
        if(t.eq.73) filename='val73.dat'
        if(t.eq.74) filename='val74.dat'
        if(t.eq.75) filename='val75.dat'
        if(t.eq.76) filename='val76.dat'
        if(t.eq.77) filename='val77.dat'
        if(t.eq.78) filename='val78.dat'
        if(t.eq.79) filename='val79.dat'
        if(t.eq.80) filename='val80.dat'
       end if
       end if
       if(flagBeq.eq.1) then
       if(flag.eq.1) then
        if(t.eq.1) filename='pob01.dat'
        if(t.eq.2) filename='pob02.dat'
        if(t.eq.3) filename='pob03.dat'
        if(t.eq.4) filename='pob04.dat'
        if(t.eq.5) filename='pob05.dat'
        if(t.eq.6) filename='pob06.dat'
        if(t.eq.7) filename='pob07.dat'
        if(t.eq.8) filename='pob08.dat'
        if(t.eq.9) filename='pob09.dat'
        if(t.eq.10) filename='pob10.dat'
        if(t.eq.11) filename='pob11.dat'
        if(t.eq.12) filename='pob12.dat'
        if(t.eq.13) filename='pob13.dat'
        if(t.eq.14) filename='pob14.dat'
        if(t.eq.15) filename='pob15.dat'
        if(t.eq.16) filename='pob16.dat'
        if(t.eq.17) filename='pob17.dat'
        if(t.eq.18) filename='pob18.dat'
        if(t.eq.19) filename='pob19.dat'
        if(t.eq.20) filename='pob20.dat'
        if(t.eq.21) filename='pob21.dat'
        if(t.eq.22) filename='pob22.dat'
        if(t.eq.23) filename='pob23.dat'
        if(t.eq.24) filename='pob24.dat'
        if(t.eq.25) filename='pob25.dat'
        if(t.eq.26) filename='pob26.dat'
        if(t.eq.27) filename='pob27.dat'
        if(t.eq.28) filename='pob28.dat'
        if(t.eq.29) filename='pob29.dat'
        if(t.eq.30) filename='pob30.dat'
        if(t.eq.31) filename='pob31.dat'
        if(t.eq.32) filename='pob32.dat'
        if(t.eq.33) filename='pob33.dat'
        if(t.eq.34) filename='pob34.dat'
        if(t.eq.35) filename='pob35.dat'
        if(t.eq.36) filename='pob36.dat'
        if(t.eq.37) filename='pob37.dat'
        if(t.eq.38) filename='pob38.dat'
        if(t.eq.39) filename='pob39.dat'
        if(t.eq.40) filename='pob40.dat'
        if(t.eq.41) filename='pob41.dat'
        if(t.eq.42) filename='pob42.dat'
        if(t.eq.43) filename='pob43.dat'
        if(t.eq.44) filename='pob44.dat'
        if(t.eq.45) filename='pob45.dat'
        if(t.eq.46) filename='pob46.dat'
        if(t.eq.47) filename='pob47.dat'
        if(t.eq.48) filename='pob48.dat'
        if(t.eq.49) filename='pob49.dat'
        if(t.eq.50) filename='pob50.dat'
        if(t.eq.51) filename='pob51.dat'
        if(t.eq.52) filename='pob52.dat'
        if(t.eq.53) filename='pob53.dat'
        if(t.eq.54) filename='pob54.dat'
        if(t.eq.55) filename='pob55.dat'
        if(t.eq.56) filename='pob56.dat'
        if(t.eq.57) filename='pob57.dat'
        if(t.eq.58) filename='pob58.dat'
        if(t.eq.59) filename='pob59.dat'
        if(t.eq.60) filename='pob60.dat'
        if(t.eq.61) filename='pob61.dat'
        if(t.eq.62) filename='pob62.dat'
        if(t.eq.63) filename='pob63.dat'
        if(t.eq.64) filename='pob64.dat'
        if(t.eq.65) filename='pob65.dat'
        if(t.eq.66) filename='pob66.dat'
        if(t.eq.67) filename='pob67.dat'
        if(t.eq.68) filename='pob68.dat'
        if(t.eq.69) filename='pob69.dat'
        if(t.eq.70) filename='pob70.dat'
        if(t.eq.71) filename='pob71.dat'
        if(t.eq.72) filename='pob72.dat'
        if(t.eq.73) filename='pob73.dat'
        if(t.eq.74) filename='pob74.dat'
        if(t.eq.75) filename='pob75.dat'
        if(t.eq.76) filename='pob76.dat'
        if(t.eq.77) filename='pob77.dat'
        if(t.eq.78) filename='pob78.dat'
        if(t.eq.79) filename='pob79.dat'
        if(t.eq.80) filename='pob80.dat'
       end if
       if(flag.eq.2) then
        if(t.eq.1) filename='vab01.dat'
        if(t.eq.2) filename='vab02.dat'
        if(t.eq.3) filename='vab03.dat'
        if(t.eq.4) filename='vab04.dat'
        if(t.eq.5) filename='vab05.dat'
        if(t.eq.6) filename='vab06.dat'
        if(t.eq.7) filename='vab07.dat'
        if(t.eq.8) filename='vab08.dat'
        if(t.eq.9) filename='vab09.dat'
        if(t.eq.10) filename='vab10.dat'
        if(t.eq.11) filename='vab11.dat'
        if(t.eq.12) filename='vab12.dat'
        if(t.eq.13) filename='vab13.dat'
        if(t.eq.14) filename='vab14.dat'
        if(t.eq.15) filename='vab15.dat'
        if(t.eq.16) filename='vab16.dat'
        if(t.eq.17) filename='vab17.dat'
        if(t.eq.18) filename='vab18.dat'
        if(t.eq.19) filename='vab19.dat'
        if(t.eq.20) filename='vab20.dat'
        if(t.eq.21) filename='vab21.dat'
        if(t.eq.22) filename='vab22.dat'
        if(t.eq.23) filename='vab23.dat'
        if(t.eq.24) filename='vab24.dat'
        if(t.eq.25) filename='vab25.dat'
        if(t.eq.26) filename='vab26.dat'
        if(t.eq.27) filename='vab27.dat'
        if(t.eq.28) filename='vab28.dat'
        if(t.eq.29) filename='vab29.dat'
        if(t.eq.30) filename='vab30.dat'
        if(t.eq.31) filename='vab31.dat'
        if(t.eq.32) filename='vab32.dat'
        if(t.eq.33) filename='vab33.dat'
        if(t.eq.34) filename='vab34.dat'
        if(t.eq.35) filename='vab35.dat'
        if(t.eq.36) filename='vab36.dat'
        if(t.eq.37) filename='vab37.dat'
        if(t.eq.38) filename='vab38.dat'
        if(t.eq.39) filename='vab39.dat'
        if(t.eq.40) filename='vab40.dat'
        if(t.eq.41) filename='vab41.dat'
        if(t.eq.42) filename='vab42.dat'
        if(t.eq.43) filename='vab43.dat'
        if(t.eq.44) filename='vab44.dat'
        if(t.eq.45) filename='vab45.dat'
        if(t.eq.46) filename='vab46.dat'
        if(t.eq.47) filename='vab47.dat'
        if(t.eq.48) filename='vab48.dat'
        if(t.eq.49) filename='vab49.dat'
        if(t.eq.50) filename='vab50.dat'
        if(t.eq.51) filename='vab51.dat'
        if(t.eq.52) filename='vab52.dat'
        if(t.eq.53) filename='vab53.dat'
        if(t.eq.54) filename='vab54.dat'
        if(t.eq.55) filename='vab55.dat'
        if(t.eq.56) filename='vab56.dat'
        if(t.eq.57) filename='vab57.dat'
        if(t.eq.58) filename='vab58.dat'
        if(t.eq.59) filename='vab59.dat'
        if(t.eq.60) filename='vab60.dat'
        if(t.eq.61) filename='vab61.dat'
        if(t.eq.62) filename='vab62.dat'
        if(t.eq.63) filename='vab63.dat'
        if(t.eq.64) filename='vab64.dat'
        if(t.eq.65) filename='vab65.dat'
        if(t.eq.66) filename='vab66.dat'
        if(t.eq.67) filename='vab67.dat'
        if(t.eq.68) filename='vab68.dat'
        if(t.eq.69) filename='vab69.dat'
        if(t.eq.70) filename='vab70.dat'
        if(t.eq.71) filename='vab71.dat'
        if(t.eq.72) filename='vab72.dat'
        if(t.eq.73) filename='vab73.dat'
        if(t.eq.74) filename='vab74.dat'
        if(t.eq.75) filename='vab75.dat'
        if(t.eq.76) filename='vab76.dat'
        if(t.eq.77) filename='vab77.dat'
        if(t.eq.78) filename='vab78.dat'
        if(t.eq.79) filename='vab79.dat'
        if(t.eq.80) filename='vab80.dat'
       end if
       end if

      end
!-------------------------------------
      subroutine getfilename(filename,t,flag,flagBeq)
      implicit none
      character(len=9) filename
      integer t,flag,flagBeq

       if(flagBeq.eq.0) then
       if(flag.eq.1) then
        if(t.eq.1) filename='pol01.txt'
        if(t.eq.2) filename='pol02.txt'
        if(t.eq.3) filename='pol03.txt'
        if(t.eq.4) filename='pol04.txt'
        if(t.eq.5) filename='pol05.txt'
        if(t.eq.6) filename='pol06.txt'
        if(t.eq.7) filename='pol07.txt'
        if(t.eq.8) filename='pol08.txt'
        if(t.eq.9) filename='pol09.txt'
        if(t.eq.10) filename='pol10.txt'
        if(t.eq.11) filename='pol11.txt'
        if(t.eq.12) filename='pol12.txt'
        if(t.eq.13) filename='pol13.txt'
        if(t.eq.14) filename='pol14.txt'
        if(t.eq.15) filename='pol15.txt'
        if(t.eq.16) filename='pol16.txt'
        if(t.eq.17) filename='pol17.txt'
        if(t.eq.18) filename='pol18.txt'
        if(t.eq.19) filename='pol19.txt'
        if(t.eq.20) filename='pol20.txt'
        if(t.eq.21) filename='pol21.txt'
        if(t.eq.22) filename='pol22.txt'
        if(t.eq.23) filename='pol23.txt'
        if(t.eq.24) filename='pol24.txt'
        if(t.eq.25) filename='pol25.txt'
        if(t.eq.26) filename='pol26.txt'
        if(t.eq.27) filename='pol27.txt'
        if(t.eq.28) filename='pol28.txt'
        if(t.eq.29) filename='pol29.txt'
        if(t.eq.30) filename='pol30.txt'
        if(t.eq.31) filename='pol31.txt'
        if(t.eq.32) filename='pol32.txt'
        if(t.eq.33) filename='pol33.txt'
        if(t.eq.34) filename='pol34.txt'
        if(t.eq.35) filename='pol35.txt'
        if(t.eq.36) filename='pol36.txt'
        if(t.eq.37) filename='pol37.txt'
        if(t.eq.38) filename='pol38.txt'
        if(t.eq.39) filename='pol39.txt'
        if(t.eq.40) filename='pol40.txt'
        if(t.eq.41) filename='pol41.txt'
        if(t.eq.42) filename='pol42.txt'
        if(t.eq.43) filename='pol43.txt'
        if(t.eq.44) filename='pol44.txt'
        if(t.eq.45) filename='pol45.txt'
        if(t.eq.46) filename='pol46.txt'
        if(t.eq.47) filename='pol47.txt'
        if(t.eq.48) filename='pol48.txt'
        if(t.eq.49) filename='pol49.txt'
        if(t.eq.50) filename='pol50.txt'
        if(t.eq.51) filename='pol51.txt'
        if(t.eq.52) filename='pol52.txt'
        if(t.eq.53) filename='pol53.txt'
        if(t.eq.54) filename='pol54.txt'
        if(t.eq.55) filename='pol55.txt'
        if(t.eq.56) filename='pol56.txt'
        if(t.eq.57) filename='pol57.txt'
        if(t.eq.58) filename='pol58.txt'
        if(t.eq.59) filename='pol59.txt'
        if(t.eq.60) filename='pol60.txt'
        if(t.eq.61) filename='pol61.txt'
        if(t.eq.62) filename='pol62.txt'
        if(t.eq.63) filename='pol63.txt'
        if(t.eq.64) filename='pol64.txt'
        if(t.eq.65) filename='pol65.txt'
        if(t.eq.66) filename='pol66.txt'
        if(t.eq.67) filename='pol67.txt'
        if(t.eq.68) filename='pol68.txt'
        if(t.eq.69) filename='pol69.txt'
        if(t.eq.70) filename='pol70.txt'
        if(t.eq.71) filename='pol71.txt'
        if(t.eq.72) filename='pol72.txt'
        if(t.eq.73) filename='pol73.txt'
        if(t.eq.74) filename='pol74.txt'
        if(t.eq.75) filename='pol75.txt'
        if(t.eq.76) filename='pol76.txt'
        if(t.eq.77) filename='pol77.txt'
        if(t.eq.78) filename='pol78.txt'
        if(t.eq.79) filename='pol79.txt'
        if(t.eq.80) filename='pol80.txt'
       end if
       if(flag.eq.2) then
        if(t.eq.1) filename='val01.txt'
        if(t.eq.2) filename='val02.txt'
        if(t.eq.3) filename='val03.txt'
        if(t.eq.4) filename='val04.txt'
        if(t.eq.5) filename='val05.txt'
        if(t.eq.6) filename='val06.txt'
        if(t.eq.7) filename='val07.txt'
        if(t.eq.8) filename='val08.txt'
        if(t.eq.9) filename='val09.txt'
        if(t.eq.10) filename='val10.txt'
        if(t.eq.11) filename='val11.txt'
        if(t.eq.12) filename='val12.txt'
        if(t.eq.13) filename='val13.txt'
        if(t.eq.14) filename='val14.txt'
        if(t.eq.15) filename='val15.txt'
        if(t.eq.16) filename='val16.txt'
        if(t.eq.17) filename='val17.txt'
        if(t.eq.18) filename='val18.txt'
        if(t.eq.19) filename='val19.txt'
        if(t.eq.20) filename='val20.txt'
        if(t.eq.21) filename='val21.txt'
        if(t.eq.22) filename='val22.txt'
        if(t.eq.23) filename='val23.txt'
        if(t.eq.24) filename='val24.txt'
        if(t.eq.25) filename='val25.txt'
        if(t.eq.26) filename='val26.txt'
        if(t.eq.27) filename='val27.txt'
        if(t.eq.28) filename='val28.txt'
        if(t.eq.29) filename='val29.txt'
        if(t.eq.30) filename='val30.txt'
        if(t.eq.31) filename='val31.txt'
        if(t.eq.32) filename='val32.txt'
        if(t.eq.33) filename='val33.txt'
        if(t.eq.34) filename='val34.txt'
        if(t.eq.35) filename='val35.txt'
        if(t.eq.36) filename='val36.txt'
        if(t.eq.37) filename='val37.txt'
        if(t.eq.38) filename='val38.txt'
        if(t.eq.39) filename='val39.txt'
        if(t.eq.40) filename='val40.txt'
        if(t.eq.41) filename='val41.txt'
        if(t.eq.42) filename='val42.txt'
        if(t.eq.43) filename='val43.txt'
        if(t.eq.44) filename='val44.txt'
        if(t.eq.45) filename='val45.txt'
        if(t.eq.46) filename='val46.txt'
        if(t.eq.47) filename='val47.txt'
        if(t.eq.48) filename='val48.txt'
        if(t.eq.49) filename='val49.txt'
        if(t.eq.50) filename='val50.txt'
        if(t.eq.51) filename='val51.txt'
        if(t.eq.52) filename='val52.txt'
        if(t.eq.53) filename='val53.txt'
        if(t.eq.54) filename='val54.txt'
        if(t.eq.55) filename='val55.txt'
        if(t.eq.56) filename='val56.txt'
        if(t.eq.57) filename='val57.txt'
        if(t.eq.58) filename='val58.txt'
        if(t.eq.59) filename='val59.txt'
        if(t.eq.60) filename='val60.txt'
        if(t.eq.61) filename='val61.txt'
        if(t.eq.62) filename='val62.txt'
        if(t.eq.63) filename='val63.txt'
        if(t.eq.64) filename='val64.txt'
        if(t.eq.65) filename='val65.txt'
        if(t.eq.66) filename='val66.txt'
        if(t.eq.67) filename='val67.txt'
        if(t.eq.68) filename='val68.txt'
        if(t.eq.69) filename='val69.txt'
        if(t.eq.70) filename='val70.txt'
        if(t.eq.71) filename='val71.txt'
        if(t.eq.72) filename='val72.txt'
        if(t.eq.73) filename='val73.txt'
        if(t.eq.74) filename='val74.txt'
        if(t.eq.75) filename='val75.txt'
        if(t.eq.76) filename='val76.txt'
        if(t.eq.77) filename='val77.txt'
        if(t.eq.78) filename='val78.txt'
        if(t.eq.79) filename='val79.txt'
        if(t.eq.80) filename='val80.txt'
       end if
       end if
       if(flagBeq.eq.1) then
       if(flag.eq.1) then
        if(t.eq.1) filename='pob01.txt'
        if(t.eq.2) filename='pob02.txt'
        if(t.eq.3) filename='pob03.txt'
        if(t.eq.4) filename='pob04.txt'
        if(t.eq.5) filename='pob05.txt'
        if(t.eq.6) filename='pob06.txt'
        if(t.eq.7) filename='pob07.txt'
        if(t.eq.8) filename='pob08.txt'
        if(t.eq.9) filename='pob09.txt'
        if(t.eq.10) filename='pob10.txt'
        if(t.eq.11) filename='pob11.txt'
        if(t.eq.12) filename='pob12.txt'
        if(t.eq.13) filename='pob13.txt'
        if(t.eq.14) filename='pob14.txt'
        if(t.eq.15) filename='pob15.txt'
        if(t.eq.16) filename='pob16.txt'
        if(t.eq.17) filename='pob17.txt'
        if(t.eq.18) filename='pob18.txt'
        if(t.eq.19) filename='pob19.txt'
        if(t.eq.20) filename='pob20.txt'
        if(t.eq.21) filename='pob21.txt'
        if(t.eq.22) filename='pob22.txt'
        if(t.eq.23) filename='pob23.txt'
        if(t.eq.24) filename='pob24.txt'
        if(t.eq.25) filename='pob25.txt'
        if(t.eq.26) filename='pob26.txt'
        if(t.eq.27) filename='pob27.txt'
        if(t.eq.28) filename='pob28.txt'
        if(t.eq.29) filename='pob29.txt'
        if(t.eq.30) filename='pob30.txt'
        if(t.eq.31) filename='pob31.txt'
        if(t.eq.32) filename='pob32.txt'
        if(t.eq.33) filename='pob33.txt'
        if(t.eq.34) filename='pob34.txt'
        if(t.eq.35) filename='pob35.txt'
        if(t.eq.36) filename='pob36.txt'
        if(t.eq.37) filename='pob37.txt'
        if(t.eq.38) filename='pob38.txt'
        if(t.eq.39) filename='pob39.txt'
        if(t.eq.40) filename='pob40.txt'
        if(t.eq.41) filename='pob41.txt'
        if(t.eq.42) filename='pob42.txt'
        if(t.eq.43) filename='pob43.txt'
        if(t.eq.44) filename='pob44.txt'
        if(t.eq.45) filename='pob45.txt'
        if(t.eq.46) filename='pob46.txt'
        if(t.eq.47) filename='pob47.txt'
        if(t.eq.48) filename='pob48.txt'
        if(t.eq.49) filename='pob49.txt'
        if(t.eq.50) filename='pob50.txt'
        if(t.eq.51) filename='pob51.txt'
        if(t.eq.52) filename='pob52.txt'
        if(t.eq.53) filename='pob53.txt'
        if(t.eq.54) filename='pob54.txt'
        if(t.eq.55) filename='pob55.txt'
        if(t.eq.56) filename='pob56.txt'
        if(t.eq.57) filename='pob57.txt'
        if(t.eq.58) filename='pob58.txt'
        if(t.eq.59) filename='pob59.txt'
        if(t.eq.60) filename='pob60.txt'
        if(t.eq.61) filename='pob61.txt'
        if(t.eq.62) filename='pob62.txt'
        if(t.eq.63) filename='pob63.txt'
        if(t.eq.64) filename='pob64.txt'
        if(t.eq.65) filename='pob65.txt'
        if(t.eq.66) filename='pob66.txt'
        if(t.eq.67) filename='pob67.txt'
        if(t.eq.68) filename='pob68.txt'
        if(t.eq.69) filename='pob69.txt'
        if(t.eq.70) filename='pob70.txt'
        if(t.eq.71) filename='pob71.txt'
        if(t.eq.72) filename='pob72.txt'
        if(t.eq.73) filename='pob73.txt'
        if(t.eq.74) filename='pob74.txt'
        if(t.eq.75) filename='pob75.txt'
        if(t.eq.76) filename='pob76.txt'
        if(t.eq.77) filename='pob77.txt'
        if(t.eq.78) filename='pob78.txt'
        if(t.eq.79) filename='pob79.txt'
        if(t.eq.80) filename='pob80.txt'
       end if
       if(flag.eq.2) then
        if(t.eq.1) filename='vab01.txt'
        if(t.eq.2) filename='vab02.txt'
        if(t.eq.3) filename='vab03.txt'
        if(t.eq.4) filename='vab04.txt'
        if(t.eq.5) filename='vab05.txt'
        if(t.eq.6) filename='vab06.txt'
        if(t.eq.7) filename='vab07.txt'
        if(t.eq.8) filename='vab08.txt'
        if(t.eq.9) filename='vab09.txt'
        if(t.eq.10) filename='vab10.txt'
        if(t.eq.11) filename='vab11.txt'
        if(t.eq.12) filename='vab12.txt'
        if(t.eq.13) filename='vab13.txt'
        if(t.eq.14) filename='vab14.txt'
        if(t.eq.15) filename='vab15.txt'
        if(t.eq.16) filename='vab16.txt'
        if(t.eq.17) filename='vab17.txt'
        if(t.eq.18) filename='vab18.txt'
        if(t.eq.19) filename='vab19.txt'
        if(t.eq.20) filename='vab20.txt'
        if(t.eq.21) filename='vab21.txt'
        if(t.eq.22) filename='vab22.txt'
        if(t.eq.23) filename='vab23.txt'
        if(t.eq.24) filename='vab24.txt'
        if(t.eq.25) filename='vab25.txt'
        if(t.eq.26) filename='vab26.txt'
        if(t.eq.27) filename='vab27.txt'
        if(t.eq.28) filename='vab28.txt'
        if(t.eq.29) filename='vab29.txt'
        if(t.eq.30) filename='vab30.txt'
        if(t.eq.31) filename='vab31.txt'
        if(t.eq.32) filename='vab32.txt'
        if(t.eq.33) filename='vab33.txt'
        if(t.eq.34) filename='vab34.txt'
        if(t.eq.35) filename='vab35.txt'
        if(t.eq.36) filename='vab36.txt'
        if(t.eq.37) filename='vab37.txt'
        if(t.eq.38) filename='vab38.txt'
        if(t.eq.39) filename='vab39.txt'
        if(t.eq.40) filename='vab40.txt'
        if(t.eq.41) filename='vab41.txt'
        if(t.eq.42) filename='vab42.txt'
        if(t.eq.43) filename='vab43.txt'
        if(t.eq.44) filename='vab44.txt'
        if(t.eq.45) filename='vab45.txt'
        if(t.eq.46) filename='vab46.txt'
        if(t.eq.47) filename='vab47.txt'
        if(t.eq.48) filename='vab48.txt'
        if(t.eq.49) filename='vab49.txt'
        if(t.eq.50) filename='vab50.txt'
        if(t.eq.51) filename='vab51.txt'
        if(t.eq.52) filename='vab52.txt'
        if(t.eq.53) filename='vab53.txt'
        if(t.eq.54) filename='vab54.txt'
        if(t.eq.55) filename='vab55.txt'
        if(t.eq.56) filename='vab56.txt'
        if(t.eq.57) filename='vab57.txt'
        if(t.eq.58) filename='vab58.txt'
        if(t.eq.59) filename='vab59.txt'
        if(t.eq.60) filename='vab60.txt'
        if(t.eq.61) filename='vab61.txt'
        if(t.eq.62) filename='vab62.txt'
        if(t.eq.63) filename='vab63.txt'
        if(t.eq.64) filename='vab64.txt'
        if(t.eq.65) filename='vab65.txt'
        if(t.eq.66) filename='vab66.txt'
        if(t.eq.67) filename='vab67.txt'
        if(t.eq.68) filename='vab68.txt'
        if(t.eq.69) filename='vab69.txt'
        if(t.eq.70) filename='vab70.txt'
        if(t.eq.71) filename='vab71.txt'
        if(t.eq.72) filename='vab72.txt'
        if(t.eq.73) filename='vab73.txt'
        if(t.eq.74) filename='vab74.txt'
        if(t.eq.75) filename='vab75.txt'
        if(t.eq.76) filename='vab76.txt'
        if(t.eq.77) filename='vab77.txt'
        if(t.eq.78) filename='vab78.txt'
        if(t.eq.79) filename='vab79.txt'
        if(t.eq.80) filename='vab80.txt'
       end if
       end if

      end

!---------------------------------------------------------------------------
      SUBROUTINE interpAgg(HousePriceGrid,nAgg,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     Wage,Rent1,Rent2,RP1,RP2,H1last,H2last,iHF,HousePrice)
      implicit none
      integer nAgg,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF
      integer iWage,iRent1,iRent2,iRP1,iRP2,iH1,iH2,iHF,iAgg
      integer jH1,jH2,jRent1,jRent2,jRP1,jRP2,jWage
      integer iAggGrid(2,2,2,2,2,2,2),tempI1
      real tempR1
      real WageGrid(nWage),Rent1grid(nRent1),Rent2grid(nRent2)
      real RP1grid(nRP1),RP2grid(nRP2),H1grid(nH1),H2grid(nH2)
      real multWage,multH1,multH2,multRent1,multRent2,multRP1,multRP2
      real Wage,Rent1,Rent2,RP1,RP2,H1last,H2last
      real HousePriceGrid(nAgg,1)
      real HousePrice7(2,2,2,2,2,2,2),HousePrice6(2,2,2,2,2,2)
      real HousePrice5(2,2,2,2,2),HousePrice4(2,2,2,2),HousePrice
      real HousePrice3(2,2,2),HousePrice2(2,2),HousePrice1(2)

      call findspot(WageGrid,nWage,Wage,nint(real(nWage)*0.5),iWage)
      call findspot(H1grid,nH1,H1last,nint(real(nH1)*0.5),iH1)
      call findspot(H2grid,nH2,H2last,nint(real(nH2)*0.5),iH2)
      call findspot(Rent1grid,nRent1,Rent1,nint(real(nRent1)*0.5),
     1 iRent1)
      call findspot(Rent2grid,nRent2,Rent2,nint(real(nRent2)*0.5),
     1 iRent2)
      call findspot(RP1grid,nRP1,RP1,nint(real(nRP1)*0.5),iRP1)
      call findspot(RP2grid,nRP2,RP2,nint(real(nRP2)*0.5),iRP2)

      multWage=(Wage-WageGrid(iWage))/
     1         (WageGrid(iWage+1)-WageGrid(iWage))
      multH1=(H1last-H1grid(iH1))/(H1grid(iH1+1)-H1grid(iH1))
      multH2=(H2last-H2grid(iH2))/(H2grid(iH2+1)-H2grid(iH2))
      multRP1=(RP1-RP1grid(iRP1))/(RP1grid(iRP1+1)-RP1grid(iRP1))
      multRP2=(RP2-RP2grid(iRP2))/(RP2grid(iRP2+1)-RP2grid(iRP2))
      multRent1=(Rent1-Rent1grid(iRent1))/
     1          (Rent1grid(iRent1+1)-Rent1grid(iRent1))
      multRent2=(Rent2-Rent2grid(iRent2))/
     1          (Rent2grid(iRent2+1)-Rent2grid(iRent2))
      if(multWage.lt.0.0) multWage=0.0
      if(multWage.gt.1.0) multWage=1.0
      if(multRent1.lt.0.0) multRent1=0.0
      if(multRent1.gt.1.0) multRent1=1.0
      if(multRent2.lt.0.0) multRent2=0.0
      if(multRent2.gt.1.0) multRent2=1.0
      if(multRP1.lt.0.0) multRP1=0.0
      if(multRP1.gt.1.0) multRP1=1.0
      if(multRP2.lt.0.0) multRP2=0.0
      if(multRP2.gt.1.0) multRP2=1.0
      if(multH1.lt.0.0) multH1=0.0
      if(multH1.gt.1.0) multH1=1.0
      if(multH2.lt.0.0) multH2=0.0
      if(multH2.gt.1.0) multH2=1.0


      do jWage=1,2
       do jRent1=1,2
        do jRent2=1,2
         do jRP1=1,2
          do jRP2=1,2
           do jH1=1,2
            do jH2=1,2

             iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1         (iWage+(jWage-1)-1)*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRent1+(jRent1-1)-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRent2+(jRent2-1)-1)*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRP1+(jRP1-1)-1)*nRP2*nH1*nH2*nHF+
     1         (iRP2+(jRP2-1)-1)*nH1*nH2*nHF+
     1         (iH1+(jH1-1)-1)*nH2*nHF+
     1         (iH2+(jH2-1)-1)*nHF+iHF
             tempI1=iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)
             HousePrice7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1         HousePriceGrid(tempI1,1)
            end do !jH2
            HousePrice6(jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1        HousePrice7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1       (HousePrice7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1        HousePrice7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
           end do  !jH1
           HousePrice5(jWage,jRent1,jRent2,jRP1,jRP2)=
     1        HousePrice6(jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1       (HousePrice6(jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1        HousePrice6(jWage,jRent1,jRent2,jRP1,jRP2,1))
          end do !jRP2
          HousePrice4(jWage,jRent1,jRent2,jRP1)=
     1        HousePrice5(jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1       (HousePrice5(jWage,jRent1,jRent2,jRP1,2)-
     1        HousePrice5(jWage,jRent1,jRent2,jRP1,1))
         end do !jRP1
         HousePrice3(jWage,jRent1,jRent2)=
     1        HousePrice4(jWage,jRent1,jRent2,1)+multRP1*
     1       (HousePrice4(jWage,jRent1,jRent2,2)-
     1        HousePrice4(jWage,jRent1,jRent2,1))
        end do !jRent2
        HousePrice2(jWage,jRent1)=
     1        HousePrice3(jWage,jRent1,1)+multRent2*
     1       (HousePrice3(jWage,jRent1,2)-HousePrice3(jWage,jRent1,1))
       end do !jRent1
       HousePrice1(jWage)=
     1        HousePrice2(jWage,1)+multRent1*
     1       (HousePrice2(jWage,2)-HousePrice2(jWage,1))
      end do !jWage
      HousePrice=HousePrice1(1)+multWage*(HousePrice1(2)-HousePrice1(1))

      end

!---------------------------------------------------------------------------
!This speeds up getpolicy by interpolating over NW last. Because all the other interpolation is identical across all agents with the same (iAge,iDZ,iNW), it is only done once, ahead of time for one such agent and then used for all others
      SUBROUTINE getpolicy0(policy,dPolicyNW,dValFunNW,
     1     ValFunCond,PensionGrid,
     1     nDZ,nRClast,nAge,nAgent,nAgg,nInd,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nLOC,nRC,NWgridAll,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     Wage,Rent1,Rent2,RP1,RP2,H1last,H2last,iHF,
     1     AgeInd,iZind,NWind,Zind,Cind,Hind,LOCind,RenterInd,
     1     RClastInd,ValFunInd,
     1     Pension,TieBreaker,RCreceiver,t,iClMkt,gamma0,alphaN)
      implicit none
      integer nAgg,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nAgent
      integer iWage,iRent1,iRent2,iRP1,iRP2,iH1,iH2,iHF,iAgg,nAge,nDZ,i
      integer jH1,jH2,jRent1,jRent2,jRP1,jRP2,jWage,jNW,iState,nRC
      integer nLOC,iChoiceDisc,iAggGrid(2,2,2,2,2,2,2),tempI1,t,iClMkt
      integer iNW(nAgent),iIndCount(nInd*nAge),RCreceiver(nAgent)
      integer AgeInd(nAgent),iZind(nAgent),iInd(nAgent),iInd0,nInd
      integer flagChoiceDisc,nRClast,RClastInd(nAgent)
      real tempR1,tempR2
      real WageGrid(nWage),Rent1grid(nRent1),Rent2grid(nRent2)
      real RP1grid(nRP1),RP2grid(nRP2),H1grid(nH1),H2grid(nH2)
      real NWgrid(nNW),NWgridAll(nAge*nDZ,nNW),NWdisc(nAgent,2)
      real multNW(nAgent),TieBreaker(nAgent,(2+nRC)*nLOC)
      real multWage,multH1,multH2,multRent1,multRent2,multRP1,multRP2
      real Wage,Rent1,Rent2,RP1,RP2,H1last,H2last,gamma0,alphaN
      real NWind(nAgent),Zind(nAgent)
      integer LOCind(nAgent),RenterInd(nAgent),extrap(2)
      integer iChoiceDisc1,iChoiceDisc2,countAgents,tempI2
      real policy(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real ValFunCond(nAge*nAgg*nInd,(2+nRC)*nLOC+1)
      real dPolicyNW(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real dValFunNW(nAge*nAgg*nInd,(2+nRC)*nLOC+1)
      real PensionGrid(nAgg),Pension
      real dV8(2,2,2,2,2,2,2,2),dV7(2,2,2,2,2,2,2)
      real dV6(2,2,2,2,2,2),dV5(2,2,2,2,2),dV4(2,2,2,2)
      real dV3(2,2,2),dV2(2,2),dV1(2,(2+nRC)*nLOC)
      real Vind8(2,2,2,2,2,2,2,2),Cind8(2,2,2,2,2,2,2,2)
      real Hind8(2,2,2,2,2,2,2,2),VindMax8(2,2,2,2,2,2,2,2)
      real VindMax7(2,2,2,2,2,2,2),VindMax6(2,2,2,2,2,2)
      real VindMax5(2,2,2,2,2),VindMax1(2)
      real VindMax4(2,2,2,2),VindMax3(2,2,2),VindMax2(2,2)
      real Vind7(2,2,2,2,2,2,2),Vind6(2,2,2,2,2,2),Vind5(2,2,2,2,2)
      real Vind4(2,2,2,2),Vind3(2,2,2),Vind2(2,2),PensInd1(2)
      real Cind7(2,2,2,2,2,2,2),Cind6(2,2,2,2,2,2),Cind5(2,2,2,2,2)
      real Cind4(2,2,2,2),Cind3(2,2,2),Cind2(2,2),Cind(nAgent)
      real Hind7(2,2,2,2,2,2,2),Hind6(2,2,2,2,2,2),Hind5(2,2,2,2,2)
      real Hind4(2,2,2,2),Hind3(2,2,2),Hind2(2,2),Hind(nAgent)
      real PensInd7(2,2,2,2,2,2,2),PensInd6(2,2,2,2,2,2),PensInd3(2,2,2)
      real PensInd5(2,2,2,2,2),PensInd4(2,2,2,2),PensInd2(2,2)
      real Cind1(2,(2+nRC)*nLOC),Hind1(2,(2+nRC)*nLOC)
      real Vind1(2,(2+nRC)*nLOC),VindCond((2+nRC)*nLOC)
      real CindCond((2+nRC)*nLOC),HindCond((2+nRC)*nLOC)
      real ValFunInd(nAgent),Normalize(nAgent)

      call findspot(WageGrid,nWage,Wage,nint(real(nWage)*0.5),iWage)
      call findspot(H1grid,nH1,H1last,nint(real(nH1)*0.5),iH1)
      call findspot(H2grid,nH2,H2last,nint(real(nH2)*0.5),iH2)
      call findspot(Rent1grid,nRent1,Rent1,nint(real(nRent1)*0.5),
     1 iRent1)
      call findspot(Rent2grid,nRent2,Rent2,nint(real(nRent2)*0.5),
     1 iRent2)
      call findspot(RP1grid,nRP1,RP1,nint(real(nRP1)*0.5),iRP1)
      call findspot(RP2grid,nRP2,RP2,nint(real(nRP2)*0.5),iRP2)

      multWage=(Wage-WageGrid(iWage))/
     1         (WageGrid(iWage+1)-WageGrid(iWage))
      multH1=(H1last-H1grid(iH1))/(H1grid(iH1+1)-H1grid(iH1))
      multH2=(H2last-H2grid(iH2))/(H2grid(iH2+1)-H2grid(iH2))
      multRP1=(RP1-RP1grid(iRP1))/(RP1grid(iRP1+1)-RP1grid(iRP1))
      multRP2=(RP2-RP2grid(iRP2))/(RP2grid(iRP2+1)-RP2grid(iRP2))
      multRent1=(Rent1-Rent1grid(iRent1))/
     1          (Rent1grid(iRent1+1)-Rent1grid(iRent1))
      multRent2=(Rent2-Rent2grid(iRent2))/
     1          (Rent2grid(iRent2+1)-Rent2grid(iRent2))
!      if(multWage.lt.0.0) multWage=0.0
!      if(multWage.gt.1.0) multWage=1.0
!      if(multRent1.lt.0.0) multRent1=0.0
!      if(multRent1.gt.1.0) multRent1=1.0
!      if(multRent2.lt.0.0) multRent2=0.0
!      if(multRent2.gt.1.0) multRent2=1.0
!      if(multRP1.lt.0.0) multRP1=0.0
!      if(multRP1.gt.1.0) multRP1=1.0
!      if(multRP2.lt.0.0) multRP2=0.0
!      if(multRP2.gt.1.0) multRP2=1.0
!      if(multH1.lt.0.0) multH1=0.0
!      if(multH1.gt.1.0) multH1=1.0
!      if(multH2.lt.0.0) multH2=0.0
!      if(multH2.gt.1.0) multH2=1.0

      do jWage=1,2
       do jRent1=1,2
        do jRent2=1,2
         do jRP1=1,2
          do jRP2=1,2
           do jH1=1,2
            do jH2=1,2

             iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1         (iWage+(jWage-1)-1)*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRent1+(jRent1-1)-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRent2+(jRent2-1)-1)*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRP1+(jRP1-1)-1)*nRP2*nH1*nH2*nHF+
     1         (iRP2+(jRP2-1)-1)*nH1*nH2*nHF+
     1         (iH1+(jH1-1)-1)*nH2*nHF+
     1         (iH2+(jH2-1)-1)*nHF+iHF
             tempI1=iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)
             PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1         PensionGrid(tempI1)
            end do !jH2
            PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1        PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1       (PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1        PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
           end do  !jH1
           PensInd5(jWage,jRent1,jRent2,jRP1,jRP2)=
     1        PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1       (PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1        PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,1))
          end do !jRP2
          PensInd4(jWage,jRent1,jRent2,jRP1)=
     1        PensInd5(jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1       (PensInd5(jWage,jRent1,jRent2,jRP1,2)-
     1        PensInd5(jWage,jRent1,jRent2,jRP1,1))
         end do !jRP1
         PensInd3(jWage,jRent1,jRent2)=
     1        PensInd4(jWage,jRent1,jRent2,1)+multRP1*
     1       (PensInd4(jWage,jRent1,jRent2,2)-
     1        PensInd4(jWage,jRent1,jRent2,1))
        end do !jRent2
        PensInd2(jWage,jRent1)=
     1        PensInd3(jWage,jRent1,1)+multRent2*
     1       (PensInd3(jWage,jRent1,2)-PensInd3(jWage,jRent1,1))
       end do !jRent1
       PensInd1(jWage)=
     1        PensInd2(jWage,1)+multRent1*
     1       (PensInd2(jWage,2)-PensInd2(jWage,1))
      end do !jWage
      Pension=PensInd1(1)+multWage*(PensInd1(2)-PensInd1(1))

!c$omp parallel
!c$omp& default(none)
!c$omp& shared(i,nAgent,nInd,NWind,NWgrid,nNW,iNW,multNW,iInd,AgeInd,
!c$omp& iZind,Normalize,iHF,t,iClMkt)
!c$omp& private(tempR1,tempI1)
!c$omp do
!
!      do i=1,nAgent
!       !Normalize(i)=Zind(i)  !Permanent Shock
!       Normalize(i)=1.0       !Stationary Shock
!       tempR1=NWind(i)/Normalize(i)
!       call findspot(NWgrid,nNW,tempR1,nint(real(nNW)*0.5),tempI1)
!       iNW(i)=tempI1
!       multNW(i)=(tempR1-NWgrid(iNW(i)))/
!     1           (NWgrid(iNW(i)+1)-NWgrid(iNW(i)))
!       iInd(i)=(AgeInd(i)-1)*nInd+(iZind(i)-1)*nNW+iNW(i)
!      end do
!
!c$omp end do
!c$omp end parallel

c$omp parallel
c$omp& default(none)
c$omp& shared(tempI1,nAge,nDZ,nAgent,nInd,NWind,NWgridAll,nNW,iNW,
c$omp& multNW,iInd,Normalize,AgeInd,iZind,iHF,t,iClMkt,NWdisc,RClastInd)
c$omp& private(i,tempR1,tempI2,NWgrid)
c$omp do

      do tempI1=1,nAge*nDZ
       do tempI2=1,nNW
        NWgrid(tempI2)=NWgridAll(tempI1,tempI2)
       end do
       do i=1,nAgent
        if((AgeInd(i)-1)*nDZ+iZind(i).eq.tempI1) then
        !Normalize(i)=Zind(i)  !Permanent Shock
         Normalize(i)=1.0       !Stationary Shock
         tempR1=NWind(i)/Normalize(i)
         call findspot(NWgrid,nNW,tempR1,nint(real(nNW)*0.5),tempI2)
         iNW(i)=tempI2
         NWdisc(i,1)=NWgrid(iNW(i))
         NWdisc(i,2)=NWgrid(iNW(i)+1)
         multNW(i)=(tempR1-NWgrid(iNW(i)))/
     1             (NWgrid(iNW(i)+1)-NWgrid(iNW(i)))
         iInd(i)=(AgeInd(i)-1)*nInd+
     1           (RClastInd(i)-1)*nDZ*nNW+(iZind(i)-1)*nNW+iNW(i)
        end if
       end do
      end do

c$omp end do
c$omp end parallel



      do i=1,nInd*nAge
       iIndCount(i)=0
      end do
      do i=1,nAgent
       iIndCount(iInd(i))=iIndCount(iInd(i))+1
      end do

c$omp parallel
c$omp& default(none)
c$omp& shared(iInd0,nRC,nAgg,nInd,nAge,nAgent,nLOC,iInd,iAggGrid,
c$omp& multWage,multRent1,multRent2,multRP1,multRP2,multH1,multH2,
c$omp& multNW,RenterInd,LOCind,Cind,Hind,ValFunInd,TieBreaker,t,iHF,
c$omp& gamma0,alphaN,iClMkt,Normalize,iIndCount,policy,ValFunCond,
c$omp& RCreceiver,dValFunNW,iNW,NWind,NWdisc,AgeInd,iZind)
c$omp& private(i,iAgg,iState,jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2,jNW,
c$omp& Cind8,Cind7,Cind6,Cind5,Cind4,Cind3,Cind2,Cind1,CindCond,
c$omp& Hind8,Hind7,Hind6,Hind5,Hind4,Hind3,Hind2,Hind1,HindCond,
c$omp& Vind8,Vind7,Vind6,Vind5,Vind4,Vind3,Vind2,Vind1,VindCond,
c$omp& iChoiceDisc,iChoiceDisc1,iChoiceDisc2,countAgents,VindMax4,
c$omp& tempI1,tempR1,tempR2,VindMax8,VindMax7,VindMax6,VindMax5,
c$omp& VindMax3,VindMax2,VindMax1,dV8,dV7,dV6,dV5,dV4,dV3,dV2,dV1,
c$omp& tempI2,extrap)
c$omp do

      do iInd0=1,nInd*nAge

      if(iIndCount(iInd0).gt.0) then

      countAgents=0

      do i=1,nAgent

      if(iInd(i).eq.iInd0) then

      countAgents=countAgents+1

      do iChoiceDisc=1,(2+nRC)*nLOC

      if(countAgents.eq.1) then !only do the interpolation for the first agent. For all others, use the first agent's Cind1,Hind1,Vind1

      do jNW=1,2

      do jWage=1,2
       do jRent1=1,2
        do jRent2=1,2
         do jRP1=1,2
          do jRP2=1,2
           do jH1=1,2
            do jH2=1,2
             iAgg=iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)
             iState=(iInd(i)+(jNW-1)-1)*nAgg+iAgg
!             if(iChoiceDisc.eq.1) then
!              VindMax8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
!     1             ValFunCond(iState,(2+nRC)*nLOC+1)
!              dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
!     1             dValFunNW(iState,1)
!             end if
!             dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
!     1             dValFunNW(iState,iChoiceDisc)
             Vind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1             ValFunCond(iState,iChoiceDisc)
             Cind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1             policy(iState,(iChoiceDisc-1)*2+1)
             Hind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1             policy(iState,(iChoiceDisc-1)*2+2)
            end do !jH2
!            if(iChoiceDisc.eq.1) then
!             VindMax7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
!     1         VindMax8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
!     1        (VindMax8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
!     1         VindMax8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
!             dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
!     1         dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
!     1        (dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
!     1         dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
!            end if
!            dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
!     1         dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
!     1        (dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
!     1         dV8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
            Cind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1            Cind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1           (Cind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1            Cind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
            Hind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1            Hind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1           (Hind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1            Hind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
            Vind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1            Vind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1           (Vind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1            Vind8(jNW,jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
           end do !jH1
           Cind6(jNW,jWage,jRent1,jRent2,jRP1,jRP2)=
     1            Cind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1           (Cind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1            Cind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1))
           Hind6(jNW,jWage,jRent1,jRent2,jRP1,jRP2)=
     1            Hind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1           (Hind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1            Hind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1))
           Vind6(jNW,jWage,jRent1,jRent2,jRP1,jRP2)=
     1            Vind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1           (Vind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1            Vind7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1))
!           dV6(jNW,jWage,jRent1,jRent2,jRP1,jRP2)=
!     1            dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
!     1           (dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,2)-
!     1            dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1))
!           if(iChoiceDisc.eq.1) then
!            VindMax6(jNW,jWage,jRent1,jRent2,jRP1,jRP2)=
!     1            VindMax7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
!     1           (VindMax7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,2)-
!     1            VindMax7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1))
!            dV6(jNW,jWage,jRent1,jRent2,jRP1,jRP2)=
!     1            dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
!     1           (dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,2)-
!     1            dV7(jNW,jWage,jRent1,jRent2,jRP1,jRP2,1))
!           end if
          end do !jRP2

          Cind5(jNW,jWage,jRent1,jRent2,jRP1)=
     1            Cind6(jNW,jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1           (Cind6(jNW,jWage,jRent1,jRent2,jRP1,2)-
     1            Cind6(jNW,jWage,jRent1,jRent2,jRP1,1))
          Hind5(jNW,jWage,jRent1,jRent2,jRP1)=
     1            Hind6(jNW,jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1           (Hind6(jNW,jWage,jRent1,jRent2,jRP1,2)-
     1            Hind6(jNW,jWage,jRent1,jRent2,jRP1,1))
          Vind5(jNW,jWage,jRent1,jRent2,jRP1)=
     1            Vind6(jNW,jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1           (Vind6(jNW,jWage,jRent1,jRent2,jRP1,2)-
     1            Vind6(jNW,jWage,jRent1,jRent2,jRP1,1))
!          dV5(jNW,jWage,jRent1,jRent2,jRP1)=
!     1            dV6(jNW,jWage,jRent1,jRent2,jRP1,1)+multRP2*
!     1           (dV6(jNW,jWage,jRent1,jRent2,jRP1,2)-
!     1            dV6(jNW,jWage,jRent1,jRent2,jRP1,1))
!         if(iChoiceDisc.eq.1) then
!          VindMax5(jNW,jWage,jRent1,jRent2,jRP1)=
!     1            VindMax6(jNW,jWage,jRent1,jRent2,jRP1,1)+multRP2*
!     1           (VindMax6(jNW,jWage,jRent1,jRent2,jRP1,2)-
!     1            VindMax6(jNW,jWage,jRent1,jRent2,jRP1,1))
!          dV5(jNW,jWage,jRent1,jRent2,jRP1)=
!     1            dV6(jNW,jWage,jRent1,jRent2,jRP1,1)+multRP2*
!     1           (dV6(jNW,jWage,jRent1,jRent2,jRP1,2)-
!     1            dV6(jNW,jWage,jRent1,jRent2,jRP1,1))
!          end if
         end do! jRP1
         Cind4(jNW,jWage,jRent1,jRent2)=
     1            Cind5(jNW,jWage,jRent1,jRent2,1)+multRP1*
     1           (Cind5(jNW,jWage,jRent1,jRent2,2)-
     1            Cind5(jNW,jWage,jRent1,jRent2,1))
         Hind4(jNW,jWage,jRent1,jRent2)=
     1            Hind5(jNW,jWage,jRent1,jRent2,1)+multRP1*
     1           (Hind5(jNW,jWage,jRent1,jRent2,2)-
     1            Hind5(jNW,jWage,jRent1,jRent2,1))
         Vind4(jNW,jWage,jRent1,jRent2)=
     1            Vind5(jNW,jWage,jRent1,jRent2,1)+multRP1*
     1           (Vind5(jNW,jWage,jRent1,jRent2,2)-
     1            Vind5(jNW,jWage,jRent1,jRent2,1))
!         dV4(jNW,jWage,jRent1,jRent2)=
!     1            dV5(jNW,jWage,jRent1,jRent2,1)+multRP1*
!     1           (dV5(jNW,jWage,jRent1,jRent2,2)-
!     1            dV5(jNW,jWage,jRent1,jRent2,1))
!         if(iChoiceDisc.eq.1) then
!          VindMax4(jNW,jWage,jRent1,jRent2)=
!     1            VindMax5(jNW,jWage,jRent1,jRent2,1)+multRP1*
!     1           (VindMax5(jNW,jWage,jRent1,jRent2,2)-
!     1            VindMax5(jNW,jWage,jRent1,jRent2,1))
!          dV4(jNW,jWage,jRent1,jRent2)=
!     1            dV5(jNW,jWage,jRent1,jRent2,1)+multRP1*
!     1           (dV5(jNW,jWage,jRent1,jRent2,2)-
!     1            dV5(jNW,jWage,jRent1,jRent2,1))
!         end if
        end do !jRent2
        Cind3(jNW,jWage,jRent1)=Cind4(jNW,jWage,jRent1,1)+multRent2*
     1            (Cind4(jNW,jWage,jRent1,2)-Cind4(jNW,jWage,jRent1,1))
        Hind3(jNW,jWage,jRent1)=Hind4(jNW,jWage,jRent1,1)+multRent2*
     1            (Hind4(jNW,jWage,jRent1,2)-Hind4(jNW,jWage,jRent1,1))
        Vind3(jNW,jWage,jRent1)=Vind4(jNW,jWage,jRent1,1)+multRent2*
     1            (Vind4(jNW,jWage,jRent1,2)-Vind4(jNW,jWage,jRent1,1))
!        dV3(jNW,jWage,jRent1)=dV4(jNW,jWage,jRent1,1)+multRent2*
!     1    (dV4(jNW,jWage,jRent1,2)-dV4(jNW,jWage,jRent1,1))
!        if(iChoiceDisc.eq.1) then
!         VindMax3(jNW,jWage,jRent1)=
!     1     VindMax4(jNW,jWage,jRent1,1)+multRent2*
!     1    (VindMax4(jNW,jWage,jRent1,2)-VindMax4(jNW,jWage,jRent1,1))
!         dV3(jNW,jWage,jRent1)=
!     1     dV4(jNW,jWage,jRent1,1)+multRent2*
!     1    (dV4(jNW,jWage,jRent1,2)-dV4(jNW,jWage,jRent1,1))
!        end if
       end do  !jRent1
       Cind2(jNW,jWage)=Cind3(jNW,jWage,1)+multRent1*
     1             (Cind3(jNW,jWage,2)-Cind3(jNW,jWage,1))
       Hind2(jNW,jWage)=Hind3(jNW,jWage,1)+multRent1*
     1             (Hind3(jNW,jWage,2)-Hind3(jNW,jWage,1))
       Vind2(jNW,jWage)=Vind3(jNW,jWage,1)+multRent1*
     1             (Vind3(jNW,jWage,2)-Vind3(jNW,jWage,1))
!       dV2(jNW,jWage)=dV3(jNW,jWage,1)+multRent1*
!     1               (dV3(jNW,jWage,2)-dV3(jNW,jWage,1))
!       if(iChoiceDisc.eq.1) then
!        VindMax2(jNW,jWage)=VindMax3(jNW,jWage,1)+multRent1*
!     1             (VindMax3(jNW,jWage,2)-VindMax3(jNW,jWage,1))
!
!            if(multRent2.le.multRent1) then
!             VindMax2(jNW,jWage)=
!     1         VindMax4(jNW,jWage,1,1)*(1.0-multRent1)+
!     1         VindMax4(jNW,jWage,2,2)*multRent2+
!     1         VindMax4(jNW,jWage,2,1)*(multRent1-multRent2)
!             dV2(jNW,jWage)=
!     1        dV4(jNW,jWage,1,1)*(1.0-multRent1)+
!     1        dV4(jNW,jWage,2,2)*multRent2+
!     1        dV4(jNW,jWage,2,1)*(multRent1-multRent2)
!            else
!             VindMax2(jNW,jWage)=
!     1         VindMax4(jNW,jWage,1,1)*(1.0-multRent2)+
!     1         VindMax4(jNW,jWage,2,2)*multRent1+
!     1         VindMax4(jNW,jWage,1,2)*(multRent2-multRent1)
!             dV2(jNW,jWage)=
!     1        dV4(jNW,jWage,1,1)*(1.0-multRent2)+
!     1        dV4(jNW,jWage,2,2)*multRent1+
!     1        dV4(jNW,jWage,1,2)*(multRent2-multRent1)
!            end if
!       end if
      end do !jWage
      Cind1(jNW,iChoiceDisc)=Cind2(jNW,1)+multWage*
     1                      (Cind2(jNW,2)-Cind2(jNW,1))
      Hind1(jNW,iChoiceDisc)=Hind2(jNW,1)+multWage*
     1                      (Hind2(jNW,2)-Hind2(jNW,1))
      Vind1(jNW,iChoiceDisc)=Vind2(jNW,1)+multWage*
     1                      (Vind2(jNW,2)-Vind2(jNW,1))
!      dV1(jNW,iChoiceDisc)=dV2(jNW,1)+multWage*(dV2(jNW,2)-dV2(jNW,1))
!      if(iChoiceDisc.eq.1) then
!       VindMax1(jNW)=VindMax2(jNW,1)+multWage*
!     1              (VindMax2(jNW,2)-VindMax2(jNW,1))
!       dV1(jNW)=dV2(jNW,1)+multWage*
!     1              (dV2(jNW,2)-dV2(jNW,1))
!      end if

      end do !jNW

      end if !countAgent=1

      CindCond(iChoiceDisc)=Cind1(1,iChoiceDisc)+multNW(i)*
     1                     (Cind1(2,iChoiceDisc)-Cind1(1,iChoiceDisc))
      HindCond(iChoiceDisc)=Hind1(1,iChoiceDisc)+multNW(i)*
     1                     (Hind1(2,iChoiceDisc)-Hind1(1,iChoiceDisc))
      VindCond(iChoiceDisc)=Vind1(1,iChoiceDisc)+multNW(i)*
     1                     (Vind1(2,iChoiceDisc)-Vind1(1,iChoiceDisc))
!      call CHFEV(NWdisc(iNW(i),1),NWdisc(iNW(i),2),
!     1           Vind1(1,iChoiceDisc),Vind1(2,iChoiceDisc),
!     1           dV1(1,iChoiceDisc),dV1(2,iChoiceDisc),
!     1           1,NWind(i),tempR2,extrap,tempI2)
!      if(tempR2.gt.Vind1(1,iChoiceDisc).and.
!     1   tempR2.lt.Vind1(2,iChoiceDisc)) then
!       VindCond(iChoiceDisc)=tempR2
!      end if


      end do !iChoiceDisc

!------------------
!first ignore the possibility of rent control
!find the 1st best location/renter choice (ignoring rent control)
      iChoiceDisc1=1
      iChoiceDisc2=1
      tempR1=-(10.0**30.0)
      tempR2=tempR1
      do iChoiceDisc=1,2*nLOC
       if(VindCond(iChoiceDisc).gt.tempR1) then
        tempR1=VindCond(iChoiceDisc)       !1st best
        iChoiceDisc1=iChoiceDisc           !1st best
       end if
      end do
!find the 2nd best location/renter choice (ignoring rent control)
      do iChoiceDisc=1,2*nLOC
       if(VindCond(iChoiceDisc).gt.tempR2.and.
     1    iChoiceDisc.ne.iChoiceDisc1) then
        tempR2=VindCond(iChoiceDisc)       !2nd best
        iChoiceDisc2=iChoiceDisc           !2nd best
       end if
      end do
      tempI1=iChoiceDisc1

!ignoring rent control, check whether 1st best and 2nd best are identical. if so, use tiebreaker, if not, just use 1st best
      if(abs(tempR2-tempR1)/abs(tempR1).lt.0.000001) then
       tempI1=1
       tempR1=-(10.0**30.0)
       do iChoiceDisc=1,2*nLOC
        if(VindCond(iChoiceDisc)*TieBreaker(i,iChoiceDisc).gt.
     1     tempR1.and.
     1     (iChoiceDisc.eq.iChoiceDisc1.or.
     1      iChoiceDisc.eq.iChoiceDisc2)) then
         tempR1=VindCond(iChoiceDisc)*TieBreaker(i,iChoiceDisc)
         tempI1=iChoiceDisc
        end if
       end do
      end if
!finally, for rent control winners only, check whether rent controlled choice is better than 1st best market choice
      if(RCreceiver(i).eq.1) then
       if(VindCond((3-1)*nLOC+1).gt.VindCond(tempI1))tempI1=(3-1)*nLOC+1
      end if
      if(RCreceiver(i).eq.2) then
       if(VindCond((3-1)*nLOC+2).gt.VindCond(tempI1))tempI1=(3-1)*nLOC+2
      end if

      Cind(i)=CindCond(tempI1)*Normalize(i)
      if(Cind(i).lt.0.001) Cind(i)=0.001
      Hind(i)=HindCond(tempI1)*Normalize(i)
      if(Hind(i).lt.0.0) Hind(i)=0.0
      LOCind(i)=mod(tempI1-1,nLOC)+1
      RenterInd(i)=1+((tempI1-LOCind(i))/nLOC)
!      tempR1=VindMax1(1)+multNW(i)*(VindMax1(2)-VindMax1(1))
!       call CHFEV(NWdisc(iNW(i),1),NWdisc(iNW(i),2),
!     1           VindMax1(1),VindMax1(2),dV1(1),dV1(2),
!     1           1,NWind(i),tempR2,extrap,tempI2)
!      if(tempR2.gt.VindMax1(1).and.tempR2.lt.VindMax1(2)) then
!       tempR1=tempR2
!      end if
!      ValFunInd(i)=tempR1*
!     1            (Normalize(i)**((1.0-gamma0)*(1.0-alphaN)))
      ValFunInd(i)=VindCond(tempI1)*
     1            (Normalize(i)**((1.0-gamma0)*(1.0-alphaN)))

      end if !if(iInd(i).eq.iInd0) ---> only do this for agents of this individual type

      end do !i

      end if !if(iIndCount(iInd0).gt.0) ---> only do this if this individual type has agents

      end do !iInd0

c$omp end do
c$omp end parallel


      end

!---------------------------------------------------------------------------
      SUBROUTINE getpolicy(policy,dPolicyNW,ValFunCond,PensionGrid,
     1     nAge,nAgent,nAgg,nInd,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nLOC,nRC,NWgrid,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     Wage,Rent1,Rent2,RP1,RP2,H1last,H2last,iHF,
     1     AgeInd,iZind,NWind,Zind,Cind,Hind,LOCind,RenterInd,ValFunInd,
     1     Pension,TieBreaker,t,iClMkt,gamma0,alphaN)
      implicit none
      integer nAgg,nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nAgent
      integer iWage,iRent1,iRent2,iRP1,iRP2,iH1,iH2,iHF,iAgg,iNW,nAge,i
      integer jH1,jH2,jRent1,jRent2,jRP1,jRP2,jWage,jNW,iStateL,iStateH
      integer nLOC,iChoiceDisc,iAggGrid(2,2,2,2,2,2,2),tempI1,t,iClMkt
      integer AgeInd(nAgent),iZind(nAgent),iInd,nInd,nRC
      real tempR1,tempR2
      real WageGrid(nWage),Rent1grid(nRent1),Rent2grid(nRent2)
      real RP1grid(nRP1),RP2grid(nRP2),H1grid(nH1),H2grid(nH2)
      real NWgrid(nNW),multNW,TieBreaker(nAgent,(2+nRC)*nLOC)
      real multWage,multH1,multH2,multRent1,multRent2,multRP1,multRP2
      real Wage,Rent1,Rent2,RP1,RP2,H1last,H2last,gamma0,alphaN
      real NWind(nAgent),Zind(nAgent)
      integer LOCind(nAgent),RenterInd(nAgent),extrap(2)
      integer iChoiceDisc1,iChoiceDisc2
      real policy(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real ValFunCond(nAge*nAgg*nInd,(2+nRC)*nLOC+1)
      real dPolicyNW(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real PensionGrid(nAgg),Pension
      real Vind7(2,2,2,2,2,2,2),Vind6(2,2,2,2,2,2),Vind5(2,2,2,2,2)
      real Vind4(2,2,2,2),Vind3(2,2,2),Vind2(2,2),Vind1(2),PensInd1(2)
      real Cind7(2,2,2,2,2,2,2),Cind6(2,2,2,2,2,2),Cind5(2,2,2,2,2)
      real Cind4(2,2,2,2),Cind3(2,2,2),Cind2(2,2),Cind1(2),Cind(nAgent)
      real Hind7(2,2,2,2,2,2,2),Hind6(2,2,2,2,2,2),Hind5(2,2,2,2,2)
      real Hind4(2,2,2,2),Hind3(2,2,2),Hind2(2,2),Hind1(2),Hind(nAgent)
      real PensInd7(2,2,2,2,2,2,2),PensInd6(2,2,2,2,2,2),PensInd3(2,2,2)
      real PensInd5(2,2,2,2,2),PensInd4(2,2,2,2),PensInd2(2,2)
      real CindCond(2*nLOC),HindCond(2*nLOC),VindCond(2*nLOC)
      real ValFunInd(nAgent),Normalize


!      if(t.eq.41.and.iClMkt.eq.2.and.iHF.eq.1) then
!       Wage=WageGrid(2)
!       H1last=H1grid(2)
!       H2last=H2grid(2)
!       RP1=RP1grid(1)
!       RP2=RP2grid(1)
!       !Rent1=Rent1grid(2)
!       !Rent2=Rent2grid(2)
!      end if




      call findspot(WageGrid,nWage,Wage,nint(real(nWage)*0.5),iWage)
      call findspot(H1grid,nH1,H1last,nint(real(nH1)*0.5),iH1)
      call findspot(H2grid,nH2,H2last,nint(real(nH2)*0.5),iH2)
      call findspot(Rent1grid,nRent1,Rent1,nint(real(nRent1)*0.5),
     1 iRent1)
      call findspot(Rent2grid,nRent2,Rent2,nint(real(nRent2)*0.5),
     1 iRent2)
      call findspot(RP1grid,nRP1,RP1,nint(real(nRP1)*0.5),iRP1)
      call findspot(RP2grid,nRP2,RP2,nint(real(nRP2)*0.5),iRP2)

      multWage=(Wage-WageGrid(iWage))/
     1         (WageGrid(iWage+1)-WageGrid(iWage))
      multH1=(H1last-H1grid(iH1))/(H1grid(iH1+1)-H1grid(iH1))
      multH2=(H2last-H2grid(iH2))/(H2grid(iH2+1)-H2grid(iH2))
      multRP1=(RP1-RP1grid(iRP1))/(RP1grid(iRP1+1)-RP1grid(iRP1))
      multRP2=(RP2-RP2grid(iRP2))/(RP2grid(iRP2+1)-RP2grid(iRP2))
      multRent1=(Rent1-Rent1grid(iRent1))/
     1          (Rent1grid(iRent1+1)-Rent1grid(iRent1))
      multRent2=(Rent2-Rent2grid(iRent2))/
     1          (Rent2grid(iRent2+1)-Rent2grid(iRent2))

      do jWage=1,2
       do jRent1=1,2
        do jRent2=1,2
         do jRP1=1,2
          do jRP2=1,2
           do jH1=1,2
            do jH2=1,2

             iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1         (iWage+(jWage-1)-1)*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRent1+(jRent1-1)-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRent2+(jRent2-1)-1)*nRP1*nRP2*nH1*nH2*nHF+
     1         (iRP1+(jRP1-1)-1)*nRP2*nH1*nH2*nHF+
     1         (iRP2+(jRP2-1)-1)*nH1*nH2*nHF+
     1         (iH1+(jH1-1)-1)*nH2*nHF+
     1         (iH2+(jH2-1)-1)*nHF+iHF
             tempI1=iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)
             PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1         PensionGrid(tempI1)
            end do !jH2
            PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1        PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1       (PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1        PensInd7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
           end do  !jH1
           PensInd5(jWage,jRent1,jRent2,jRP1,jRP2)=
     1        PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1       (PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1        PensInd6(jWage,jRent1,jRent2,jRP1,jRP2,1))
          end do !jRP2
          PensInd4(jWage,jRent1,jRent2,jRP1)=
     1        PensInd5(jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1       (PensInd5(jWage,jRent1,jRent2,jRP1,2)-
     1        PensInd5(jWage,jRent1,jRent2,jRP1,1))
         end do !jRP1
         PensInd3(jWage,jRent1,jRent2)=
     1        PensInd4(jWage,jRent1,jRent2,1)+multRP1*
     1       (PensInd4(jWage,jRent1,jRent2,2)-
     1        PensInd4(jWage,jRent1,jRent2,1))
        end do !jRent2
        PensInd2(jWage,jRent1)=
     1        PensInd3(jWage,jRent1,1)+multRent2*
     1       (PensInd3(jWage,jRent1,2)-PensInd3(jWage,jRent1,1))
       end do !jRent1
       PensInd1(jWage)=
     1        PensInd2(jWage,1)+multRent1*
     1       (PensInd2(jWage,2)-PensInd2(jWage,1))
      end do !jWage
      Pension=PensInd1(1)+multWage*(PensInd1(2)-PensInd1(1))

c$omp parallel
c$omp& default(none)
c$omp& shared(i,nAgg,nAgent,NWind,Zind,NWgrid,nNW,nLOC,iAggGrid,policy,
c$omp& multWage,multRent1,multRent2,multRP1,multRP2,multH1,multH2,
c$omp& ValFunCond,RenterInd,LOCind,AgeInd,Cind,Hind,TieBreaker,t,
c$omp& dPolicyNW,gamma0,alphaN,ValFunInd,iZind,nInd,iClMkt,iHF)
c$omp& private(iNW,iInd,tempR1,tempR2,multNW,
c$omp& jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2,extrap,
c$omp& iAgg,iStateL,iStateH,tempI1,Cind7,Cind6,Cind5,Cind4,Cind3,Cind2,
c$omp& Cind1,Hind7,Hind6,Hind5,Hind4,Hind3,Hind2,Hind1,Vind7,Vind6,
c$omp& Vind5,Vind4,Vind3,Vind2,Vind1,iChoiceDisc,CindCond,HindCond,
c$omp& VindCond,Normalize,iChoiceDisc1,iChoiceDisc2)
c$omp do

      do i=1,nAgent

      !Normalize=Zind(i)  !Permanent Shock
      Normalize=1.0       !Stationary Shock

      tempR1=NWind(i)/Normalize
      call findspot(NWgrid,nNW,tempR1,nint(real(nNW)*0.5),iNW)
      multNW=(tempR1-NWgrid(iNW))/(NWgrid(iNW+1)-NWgrid(iNW))

      do iChoiceDisc=1,2*nLOC

      do jWage=1,2
       do jRent1=1,2
        do jRent2=1,2
         do jRP1=1,2
          do jRP2=1,2
           do jH1=1,2
            do jH2=1,2
             iAgg=iAggGrid(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)
             iInd=(iZind(i)-1)*nNW+iNW
             iStateL=(AgeInd(i)-1)*nAgg*nInd+(iInd+(1-1)-1)*nAgg+iAgg
             iStateH=(AgeInd(i)-1)*nAgg*nInd+(iInd+(2-1)-1)*nAgg+iAgg
!             Cind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
!     1              policy(iStateL,(iChoiceDisc-1)*2+1)+multNW*
!     1             (policy(iStateH,(iChoiceDisc-1)*2+1)-
!     1              policy(iStateL,(iChoiceDisc-1)*2+1))

             call CHFEV(NWgrid(iNW),NWgrid(iNW+1),
     1              policy(iStateL,(iChoiceDisc-1)*2+1),
     1              policy(iStateH,(iChoiceDisc-1)*2+1),
     2              dPolicyNW(iStateL,(iChoiceDisc-1)*2+1),
     1              dPolicyNW(iStateH,(iChoiceDisc-1)*2+1),
     3              1,tempR1,tempR2,extrap,tempI1)
             Cind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=tempR2
             if(tempR2.lt.policy(iStateL,(iChoiceDisc-1)*2+1).or.
     1          tempR2.gt.policy(iStateH,(iChoiceDisc-1)*2+1)) then
              Cind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1              policy(iStateL,(iChoiceDisc-1)*2+1)+multNW*
     1             (policy(iStateH,(iChoiceDisc-1)*2+1)-
     1              policy(iStateL,(iChoiceDisc-1)*2+1))
             end if
             Hind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1              policy(iStateL,(iChoiceDisc-1)*2+2)+multNW*
     1             (policy(iStateH,(iChoiceDisc-1)*2+2)-
     1              policy(iStateL,(iChoiceDisc-1)*2+2))
             Vind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,jH2)=
     1              ValFunCond(iStateL,iChoiceDisc)+multNW*
     1             (ValFunCond(iStateH,iChoiceDisc)-
     1              ValFunCond(iStateL,iChoiceDisc))
            end do !jH2
            Cind6(jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1            Cind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1           (Cind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1            Cind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
            Hind6(jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1            Hind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1           (Hind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1            Hind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
            Vind6(jWage,jRent1,jRent2,jRP1,jRP2,jH1)=
     1            Vind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1)+multH2*
     1           (Vind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,2)-
     1            Vind7(jWage,jRent1,jRent2,jRP1,jRP2,jH1,1))
           end do  !jH1
           Cind5(jWage,jRent1,jRent2,jRP1,jRP2)=
     1            Cind6(jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1           (Cind6(jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1            Cind6(jWage,jRent1,jRent2,jRP1,jRP2,1))
           Hind5(jWage,jRent1,jRent2,jRP1,jRP2)=
     1            Hind6(jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1           (Hind6(jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1            Hind6(jWage,jRent1,jRent2,jRP1,jRP2,1))
           Vind5(jWage,jRent1,jRent2,jRP1,jRP2)=
     1            Vind6(jWage,jRent1,jRent2,jRP1,jRP2,1)+multH1*
     1           (Vind6(jWage,jRent1,jRent2,jRP1,jRP2,2)-
     1            Vind6(jWage,jRent1,jRent2,jRP1,jRP2,1))
          end do !jRP2
          Cind4(jWage,jRent1,jRent2,jRP1)=
     1            Cind5(jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1           (Cind5(jWage,jRent1,jRent2,jRP1,2)-
     1            Cind5(jWage,jRent1,jRent2,jRP1,1))
          Hind4(jWage,jRent1,jRent2,jRP1)=
     1            Hind5(jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1           (Hind5(jWage,jRent1,jRent2,jRP1,2)-
     1            Hind5(jWage,jRent1,jRent2,jRP1,1))
          Vind4(jWage,jRent1,jRent2,jRP1)=
     1            Vind5(jWage,jRent1,jRent2,jRP1,1)+multRP2*
     1           (Vind5(jWage,jRent1,jRent2,jRP1,2)-
     1            Vind5(jWage,jRent1,jRent2,jRP1,1))
         end do !jRP1
         Cind3(jWage,jRent1,jRent2)=
     1            Cind4(jWage,jRent1,jRent2,1)+multRP1*
     1           (Cind4(jWage,jRent1,jRent2,2)-
     1            Cind4(jWage,jRent1,jRent2,1))
         Hind3(jWage,jRent1,jRent2)=
     1            Hind4(jWage,jRent1,jRent2,1)+multRP1*
     1           (Hind4(jWage,jRent1,jRent2,2)-
     1            Hind4(jWage,jRent1,jRent2,1))
         Vind3(jWage,jRent1,jRent2)=
     1            Vind4(jWage,jRent1,jRent2,1)+multRP1*
     1           (Vind4(jWage,jRent1,jRent2,2)-
     1            Vind4(jWage,jRent1,jRent2,1))
        end do !jRent2
        Cind2(jWage,jRent1)=Cind3(jWage,jRent1,1)+multRent2*
     1                     (Cind3(jWage,jRent1,2)-Cind3(jWage,jRent1,1))
        Hind2(jWage,jRent1)=Hind3(jWage,jRent1,1)+multRent2*
     1                     (Hind3(jWage,jRent1,2)-Hind3(jWage,jRent1,1))
        Vind2(jWage,jRent1)=Vind3(jWage,jRent1,1)+multRent2*
     1                     (Vind3(jWage,jRent1,2)-Vind3(jWage,jRent1,1))
       end do !jRent1
       Cind1(jWage)=Cind2(jWage,1)+multRent1*
     1             (Cind2(jWage,2)-Cind2(jWage,1))
       Hind1(jWage)=Hind2(jWage,1)+multRent1*
     1             (Hind2(jWage,2)-Hind2(jWage,1))
       Vind1(jWage)=Vind2(jWage,1)+multRent1*
     1             (Vind2(jWage,2)-Vind2(jWage,1))
      end do !jWage

      CindCond(iChoiceDisc)=Cind1(1)+multWage*(Cind1(2)-Cind1(1))
      HindCond(iChoiceDisc)=Hind1(1)+multWage*(Hind1(2)-Hind1(1))
      VindCond(iChoiceDisc)=Vind1(1)+multWage*(Vind1(2)-Vind1(1))
      end do !iChoiceDisc


      iChoiceDisc1=1
      iChoiceDisc2=1
      tempR1=-(10.0**30.0)
      tempR2=tempR1
      do iChoiceDisc=1,2*nLOC
       if(VindCond(iChoiceDisc).gt.tempR1) then
        tempR1=VindCond(iChoiceDisc)       !1st best
        iChoiceDisc1=iChoiceDisc           !1st best
       end if
      end do
      do iChoiceDisc=1,2*nLOC
       if(VindCond(iChoiceDisc).gt.tempR2.and.
     1    iChoiceDisc.ne.iChoiceDisc1) then
        tempR2=VindCond(iChoiceDisc)
        iChoiceDisc2=iChoiceDisc
       end if
      end do
      tempI1=iChoiceDisc1

      if(abs(tempR2-tempR1)/abs(tempR1).lt.0.000001) then
       tempI1=1
       tempR1=-(10.0**30.0)
       do iChoiceDisc=1,2*nLOC
        if(VindCond(iChoiceDisc)*TieBreaker(i,iChoiceDisc).gt.
     1     tempR1.and.
     1     (iChoiceDisc.eq.iChoiceDisc1.or.
     1      iChoiceDisc.eq.iChoiceDisc2)) then
         tempR1=VindCond(iChoiceDisc)*TieBreaker(i,iChoiceDisc)
         tempI1=iChoiceDisc
        end if
       end do
      end if
      Cind(i)=CindCond(tempI1)*Normalize
      if(Cind(i).lt.0.001) Cind(i)=0.001
      Hind(i)=HindCond(tempI1)*Normalize
      if(Hind(i).lt.0.0) Hind(i)=0.0
      LOCind(i)=mod(tempI1-1,nLOC)+1
      RenterInd(i)=1+((tempI1-LOCind(i))/nLOC)
      ValFunInd(i)=VindCond(tempI1)*
     1            (Normalize**((1.0-gamma0)*(1.0-alphaN)))

      end do !iAgents

c$omp end do
c$omp end parallel

      end
!-------------------------------------------------------------
!-------------------------------------------------------------
!      This subroutine takes the product of two matricies
!      A is NxM, B is MxL
      SUBROUTINE matmult(A,B,C,N,M,L)
      implicit none
      integer N,M,L,i,j,k
      double precision A(N,M),B(M,L),C(N,L),s

      do i=1,N
      do j=1,L
       s=0
       do k=1,M
        s=s+A(i,k)*B(k,j)
       end do
       C(i,j)=s
      end do
      end do

      end

!-------------------------------------------------------------
!      This subroutine takes the product of two matricies
!      A is NxM, B is MxL
      SUBROUTINE matmultreal(A,B,C,N,M,L)
      implicit none
      integer N,M,L,i,j,k
      real A(N,M),B(M,L),C(N,L),s

      do i=1,N
      do j=1,L
       s=0
       do k=1,M
        s=s+A(i,k)*B(k,j)
       end do
       C(i,j)=s
      end do
      end do

      end

!--------------------------------------------------------------
      SUBROUTINE transpos(A,At,N,M)
      implicit none
      integer N,M,i,j
      double precision A(N,M),At(M,N)

      do i=1,N
      do j=1,M
       At(j,i)=A(i,j)
       !write(6,*) i,j,At(j,i)
      end do
      end do

      end

!--------------------------------------------------------------
!this regresses Y on X, B=((X'X)^-1)*(X'Y)
      SUBROUTINE regress(Y0,X0,T0,T,N0,N,X0in,B0,rsq)
      implicit none
      integer T0,T,N,N0,i,j,Indx(N),lwork,X0in(N0)
      real X0(T0,N0),Y0(T0,1)
      double precision X(T,N),Y(T,1),Xt(N,T),XX(N,N),XXi(N,N)
      double precision B(1,N),Bt(N,1),XY(N,1),Ypred(T,1)
      real B0(N0,1)
      real Ymean,s1,s2
      double precision rsq,work(2*N)

      do i=1,N0
       B0(i,1)=0
      end do

      lwork=2*N
      do i=1,T
       Y(i,1)=Y0(i,1)
       do j=1,N
        X(i,j)=X0(i,X0in(j))
       end do
      end do
      call transpos(X,Xt,T,N)
      call matmult(Xt,X,XX,N,T,N)
      do i=1,N
       do j=1,N
        XXi(i,j)=XX(i,j)
       end do
      end do

      !if(N.le.3) then
      ! call inverse(XX,XXi,N)
      !else
       !call migs(XX,N,XXi,Indx)

       call DGETRF(N,N,XXi,N,Indx,i)
       call DGETRI(N,XXi,N,Indx,WORK,LWORK,i)
      !end if
      call matmult(Xt,Y,XY,N,T,1)
      call matmult(XXi,XY,B,N,N,1)

      !this does Rsq
      Ymean=0
      s1=0
      s2=0
      call transpos(B,Bt,N,1)
      call matmult(X,Bt,Ypred,T,N,1)
      do i=1,T
       Ymean=Y(i,1)+Ymean
      end do
      Ymean=Ymean/real(T)
      do i=1,T
       s1=s1+(Y(i,1)-Ypred(i,1))*(Y(i,1)-Ypred(i,1))
       s2=s2+(Y(i,1)-Ymean)*(Y(i,1)-Ymean)
      end do
      rsq=1-(s1/s2)
      do i=1,N
       B0(X0in(i),1)=Bt(i,1)
      end do
!      write(6,*) 'works 7'
!      write(6,*) rsq


      end

!-------------------------------------------
      subroutine inverse(arrayin,arrayout,N)
      implicit none
      integer N,i
      double precision arrayin(N,N),arrayout(N,N),tempR1,tempR2

      if(N.eq.2) then
       tempR1=arrayin(1,2)*arrayin(1,2)-arrayin(1,1)*arrayin(2,2)
       arrayout(1,1)=-arrayin(2,2)/tempR1
       arrayout(1,2)=arrayin(2,1)/tempR1
       arrayout(2,1)=arrayin(1,2)/tempR1
       arrayout(2,2)=arrayin(1,1)/tempR1
      end if
      if(N.eq.3) then
       tempR1=(arrayin(2,3)*arrayin(1,3)-arrayin(3,3)*arrayin(1,2))/
     1        (arrayin(2,3)*arrayin(1,2)-arrayin(2,2)*arrayin(1,3))
       tempR2=(arrayin(2,2)*arrayin(3,3)-arrayin(2,3)*arrayin(2,3))/
     1        (arrayin(2,3)*arrayin(1,2)-arrayin(2,2)*arrayin(1,3))
       arrayout(1,3)=1/(arrayin(1,3)+tempR2*arrayin(1,1)+
     1               tempR1*arrayin(1,2))
       arrayout(3,1)=arrayout(1,3)
       arrayout(1,1)=arrayout(1,3)*tempR2
       arrayout(1,2)=arrayout(1,3)*tempR1
       arrayout(2,1)=arrayout(1,2)
       arrayout(3,3)=arrayout(1,3)*
     1          (arrayin(2,2)*arrayin(1,1)-arrayin(1,2)*arrayin(1,2))/
     2          (arrayin(2,3)*arrayin(1,2)-arrayin(2,2)*arrayin(1,3))
       arrayout(2,3)=-arrayout(1,3)*(arrayin(1,1)/arrayin(1,2))-
     1                arrayout(3,3)*(arrayin(1,3)/arrayin(1,2))
       arrayout(3,2)=arrayout(2,3)
       arrayout(2,2)=-arrayout(2,3)*(arrayin(1,3)/arrayin(1,2))-
     1                arrayout(1,2)*(arrayin(1,1)/arrayin(1,2))
      end if

      end

!-------------------------------------------
      subroutine clearmarkets(t,nWage,nRent1,nRent2,nAgg,nInd,nNW,nDZ,
     1  nRClast,nRP1,
     1  nRP2,nH1,nH2,nHF,nLOC,nRC,nAge,nAgent,nFirmC,nFirm1,nFirm2,
     1  nRet,NumRetired,nDepr,thetaRes,thetaInv,
     1  RTSC,RTSH0loc1,HBARloc1,RTSH0loc2,HBARloc2,deprH,deprINV0,
     1  gamma0,alphaC,alphaH,alphaN,ElastCH,ElastCN,
     1  lambda0,tau0,lambdaBase,tauBase,chi0,
     1  HoursMin,CluxCut,CluxCost,ProfitRedist,PriceBond,
     1  flagRetInd,taxss,taxprop,taxpropOOT,HresMin,RCavgrent,
     1  RCavgrentDev,RCinccut,RChsize,RCrentred,RCprob,RCprobStay,
     1  RCshare,RCshock,RCshock0,RCshock1,RCshock2,
     1  WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1  HFgrid0,HFgrid1,HFVgrid,NWgridAll,AgeProd,CommCost,CommCostFin,
     1  LeisureMin,PH1grid,PH2grid,policy,dPolicyNW,dValFunNW,
     1  ValFunCond,PensionGrid,iHFlast,
     1  iHF,Wage,Rent1,Rent2,Rent,RP1,RP2,H1last,H2last,H1,H2,PH,PHavg,
     1  Hours,HoursDemand,Cons,Hres,HresRenter,HresOwner,HresRC,Hinv,
     1  Pension,Bbeq,HObeq,HIbeq,BeqReceiver,BeqInd,RCreceiver,
     1  AgeInd,iZind,Zind,NWind,Bind,Cind,HoursInd,Hind,HresInd,
     1  HresIndLast,HindLast,RenterInd,RenterIndLast,RClastInd,
     1  LOCind,LOCindLast,
     1  LaborIncomeInd,ValFunInd,TieBreaker,SSIdist,NWmin,NWmax,
     1  DeprGrid,iDepr,outputErr,TotYears,iClMkt,flagRCstay)
      implicit none
      integer TotYears
      real WageGrid(nWage),Rent1Grid(nRent1),Rent2Grid(nRent2)
      real NWgridAll(nAge*nDZ,nNW)
      real RP1grid(nRP1),RP2grid(nRP2),SSIdist(nDZ)
      real H1grid(nH1),H2grid(nH2),HFVgrid(nHF,nLOC)
      real HFgrid0(nHF,nLOC),HFgrid1(nHF,nLOC)
      real PH1grid(nAgg,1),PH2grid(nAgg,1),NumRetired
      real RCinccut(nLOC,nHF),RChsize(nLOC,nHF),Hdem(nLOC)
      real RCrentred(nLOC,nHF),RCprob(nLOC),RCprobStay(nLOC)
      real RCprobTemp(nLOC,nRClast)
      real RCshare(nLOC,nHF),RCshock(nAgent),RCshock0(nAgent)
      real RCshock1(nAgent),RCshock2(nAgent)
      real RCavgrent(nLOC,nHF),RCprobBest(nLOC)
      real outputErr(TotYears,7)
      real nFirmC,nFirm1,nFirm2,NWmin,NWmax
      integer RCreceiver(nAgent),RCreceivercut(2),flagRCstay(nHF)
      integer t,i,j,nAgg,iClMkt,nClMkt,iClMktBreak,nAgent,nAge,iHF,nRet
      integer nWage,nRent1,nRent2,nNW,nRP1,nRP2,nH1,nH2,nHF,nLOC,nRC,nDZ
      integer iZind(nAgent),nInd,BeqReceiver(nAgent),nRClast,iHFlast
      real RTSC,RTSH0loc1,HBARloc1(nHF),RTSH0loc2,HBARloc2(nHF)
      real deprH(nLOC),deprINV0,thetaRes,thetaInv
      real gamma0,alphaN,alphaC,alphaH,ElastCH,ElastCN
      real lambda0(nHF),tau0(nHF),lambdaBase,tauBase
      real chi0,HoursMin,HresMin
      real HoursConst2(nLOC,2+nRC),HoursConst3
      real HoursDemandC,HoursDemandLOC1,HoursDemandLOC2,HoursDemand
      real Hours,Cons,BeqInd(nAgent,7),ProfitRedist(3)
      real Hres(nLOC),HresRenter(nLOC),HresOwner(nLOC),HresRC(nLOC)
      double precision upd(5),tempF1,tempF2,tempF3,tempF4,tempF5
      double precision tempF6,tempF7,tempF8,tempF9,tempF10
      double precision tempF11,tempF12,tempF13,tempF14
      integer flagRetInd(nAgent),nDepr
      real err(25,7),CountNeg(5),CluxCut(2),CluxCost(2),CluxCost0
      real errBest,WageBest,Rent1best,Rent2best,RP1best,RP2best
      real errNorm(1,7),RCprobLast(25,2)
      real Rent1last(25),Rent2last(25),WageLast(25)
      real RP1last(25),RP2last(25),LeisureMin,CommCostFin(nLOC,2)
      real Rent(nLOC),PH(nLOC),Hinv(nLOC)
      real PHavg(nLOC),PHavgMult(nLOC),taxpropOOT(nLOC)
      real AgeProd(nAge),CommCost(nLOC,2),Bbeq,HObeq(nLOC),HIbeq(nLOC)
      real Wage,Rent1,Rent2,RP1,RP2,H1last,H2last,H1,H2,taxss
      real taxprop(nHF,nLOC)
      real tempR1,tempR2,tempR3,tempR4,tempR5,tempR6,tempR7,tempR8
      real tempR9,tempR10
      integer tempI1,tempI2,tempI3,tempI4,tempI5,tempI6
      real NWind(nAgent),Bind(nAgent),Cind(nAgent),Zind(nAgent)
      real HresIndLast(nAgent),HindLast(nAgent),Hind(nAgent)
      real HoursInd(nAgent),HresInd(nAgent),LaborIncomeInd(nAgent)
      real ValFunInd(nAgent),TieBreaker(nAgent,(2+nRC)*nLOC)
      integer RenterIndLast(nAgent),RenterInd(nAgent),RClastInd(nAgent)
      integer AgeInd(nAgent),LOCind(nAgent),LOCindLast(nAgent)
      real Policy(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real dPolicyNW(nAge*nAgg*nInd,2*(2+nRC)*nLOC)
      real dValFunNW(nAge*nAgg*nInd,(2+nRC)*nLOC+1)
      real ValFunCond(nAge*nAgg*nInd,(2+nRC)*nLOC+1),PensionGrid(nAgg)
      real PensionBelief,Pension,PensionTax,PropTaxIncome
      real DeprGrid(nDepr),ForDemTot(nLOC),RCavgrentDev(nLOC,nHF)
      integer iDepr(nAgent),iHoursChoice,nAgentRClast(nLOC)
      real param1,param2,HoursConst0,HoursConst1
      real HouseConst0,HouseConst1,HouseConst2,HresMinVoucher
      real Profit,ProfitC,ProfitLOC1,ProfitLOC2,r0,PriceBond
      real HoursGrid(3,2),TaxableIncome,HSVtax,HSVtaxBase

      r0=1.0-PriceBond
      Profit=0.0
      RCreceivercut(1)=0
      RCreceivercut(2)=0
      do i=1,nAgent
       RCreceiver(i)=0
      end do
      param1=((chi0*alphaN/(alphaC*(1.0-alphaN)))**
     1       (1.0/(1.0-chi0*ElastCN)))
      param2=(1.0-ElastCN)/(1.0-chi0*ElastCN)

      do i=1,nRClast
       if (i.eq.1.or.flagRCstay(iHF).eq.0) then
        RCprobTemp(1,i)=RCprob(1)
        RCprobTemp(2,i)=RCprob(2)
       else
        if(i.eq.2) then
         RCprobTemp(1,i)=RCprobStay(1)
         RCprobTemp(2,i)=0.0
         if(RCprobTemp(1,i).lt.RCprob(1)) RCprobTemp(1,i)=RCprob(1)
        end if
        if(i.eq.3) then
         RCprobTemp(1,i)=0.0
         RCprobTemp(2,i)=RCprobStay(2)
         if(RCprobTemp(2,i).lt.RCprob(2)) RCprobTemp(2,i)=RCprob(2)
        end if
       end if
      end do
      
!Measure the number of RC agents from last period, these are the ones that may benefit from persistent RC
!set this to zero if nRClast=1, that is if there is no persistent RC
      do i=1,nLOC
       nAgentRClast(i)=0
      end do
      do i=1,nAgent
       if(nRClast.gt.1.and.RClastInd(i).gt.1) then
        nAgentRClast(LOCindLast(i))=nAgentRClast(LOCindLast(i))+1
       end if
      end do

      do i=1,25
       WageLast(i)=real(i)
       Rent1Last(i)=real(i)
       Rent2Last(i)=real(i)
       RP1Last(i)=real(i)
       RP2Last(i)=real(i)
       RCprobLast(i,1)=real(i)
       RCprobLast(i,2)=real(i)
       do j=1,7
        err(i,j)=real(mod(i,2))-0.5
       end do
      end do
      upd(1)=0.01!0.02!0.1
      upd(2)=0.002!0.004!0.02
      upd(3)=0.002!0.004!0.02
      upd(4)=0.0001!0.0002!0.001
      upd(5)=0.0001!0.0002!0.001
      errBest=10000000

      !RCprob(1)=RCshare(1,iHF)
      !RCprob(2)=RCshare(2,iHF)
      PHavgMult(1)=1.0
      PHavgMult(2)=1.0

      ForDemTot(1)=exp(HFgrid0(iHF,1)-
     1                 HFgrid1(iHF,1)*log(PH(1)*(1.0+taxpropOOT(1)))) !Foreign Demand per Domestic Household in Zone 1
      ForDemTot(2)=exp(HFgrid0(iHF,2)-
     1                 HFgrid1(iHF,2)*log(PH(2)*(1.0+taxpropOOT(2)))) !Foreign Demand per Domestic Household in Zone 2
      Hres(1)=H1last-HFVgrid(iHF,1)*ForDemTot(1)*real(nAgent)  !initializing Hres to some reasonable number
      Hres(2)=H2last-HFVgrid(iHF,2)*ForDemTot(2)*real(nAgent)  !initializing Hres to some reasonable number

      nClMkt=2000
      iClMktBreak=nClMkt
      do iClMkt=1,nClMkt


!      if(t.eq.41) then
!      if(iClMkt.eq.1) then
!       Wage=0.8860427
!       Rent1=0.0621150
!       Rent2=0.0620672
!       RP1=0.0000774
!       RP2=0.0000785
!      end if
!      if(iClMkt.eq.2) then
!       Wage=0.8860427
!       Rent1=0.0620911
!       Rent2=0.0620911
!       RP1=0.0000779
!       RP2=0.0000779
!      end if
!      end if


      Rent(1)=Rent1
      Rent(2)=Rent2

      tempR1=Rent(1)
      HoursConst2(1,1)=(alphaC+alphaH*
     1    ((alphaH/(alphaC*tempR1))**(elastCH/(1.0-elastCH))))**
     1    ((ElastCN-ElastCH)/ElastCH)     !Z1 renters
      tempR1=Rent(2)
      HoursConst2(2,1)=(alphaC+alphaH*
     1    ((alphaH/(alphaC*tempR1))**(elastCH/(1.0-elastCH))))**
     1    ((ElastCN-ElastCH)/ElastCH)     !Z2 renters
      Hoursconst2(1,2)=Hoursconst2(1,1)   !Z1 owners
      Hoursconst2(2,2)=Hoursconst2(2,1)   !Z1 owners
      tempR1=Rent(1)*(1.0-RCrentred(1,iHF))
      if(nRC.eq.1) then
       HoursConst2(1,2+nRC)=(alphaC+alphaH*
     1     ((alphaH/(alphaC*tempR1))**(elastCH/(1.0-elastCH))))**
     1     ((ElastCN-ElastCH)/ElastCH)     !Z1 RC
       tempR1=Rent(2)*(1.0-RCrentred(2,iHF))
       HoursConst2(2,2+nRC)=(alphaC+alphaH*
     1     ((alphaH/(alphaC*tempR1))**(elastCH/(1.0-elastCH))))**
     1     ((ElastCN-ElastCH)/ElastCH)     !Z2 RC
      end if

      call interpAgg(PH1grid,nAgg,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     Wage,Rent1,Rent2,RP1,RP2,
     1     H1last/real(nAgent),H2last/real(nAgent),iHF,tempR1)
      PH(1)=tempR1
      call interpAgg(PH2grid,nAgg,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     Wage,Rent1,Rent2,RP1,RP2,
     1     H1last/real(nAgent),H2last/real(nAgent),iHF,tempR1)
      PH(2)=tempR1

      PropTaxIncome=((taxprop(iHF,1)*H1last*PH(1)+
     1                taxprop(iHF,2)*H2last*PH(2))/real(nAgent))+
     1                taxpropOOT(1)*ForDemTot(1)*PH(1)+
     1                taxpropOOT(2)*ForDemTot(2)*PH(2)   ! property tax income per capita
      do i=1,nAgent
       if(RenterIndLast(i).eq.1.or.RenterIndLast(i).eq.3) then
        NWind(i)=Bind(i)
       else
        NWind(i)=Bind(i)+PH(LOCindLast(i))*
     1    (HresIndLast(i)+HindLast(i)*RCavgrent(LOCindLast(i),iHF))*
     1    (1.0-deprH(LOCindLast(i))*DeprGrid(iDepr(i))-
     1     taxprop(iHFlast,LOCindLast(i)))-
     1     PH(LOCindLast(i))*deprINV0*HindLast(i)*
     1     RCavgrent(LOCindLast(i),iHF)
       end if
       if(BeqReceiver(i).gt.0) then
!everyone receives same bequest
!        NWind(i)=NWind(i)+Bbeq+
!     1   PH(1)*HObeq(1)*(1.0-deprH(1)-taxprop(iHF))+
!     1   PH(2)*HObeq(2)*(1.0-deprH(2)-taxprop(iHF))+
!     1   PH(1)*HIbeq(1)*(1.0-deprH(1)-taxprop(iHF)-deprINV0)*RCavgrent(1,iHF)+
!     1   PH(2)*HIbeq(2)*(1.0-deprH(2)-taxprop(iHF)-deprINV0)*RCavgrent(2,iHF)
!bequest distribution is non-trivial
        j=BeqReceiver(i)
        NWind(i)=NWind(i)+BeqInd(j,1)+
     1  PH(1)*BeqInd(j,2)*
     1   (1.0-deprH(1)*DeprGrid(iDepr(j))-taxprop(iHFlast,1))+
     1  PH(2)*BeqInd(j,3)*
     1   (1.0-deprH(2)*DeprGrid(iDepr(j))-taxprop(iHFlast,2))+
     1  PH(1)*BeqInd(j,4)*
     1   (1.0-deprH(1)*DeprGrid(iDepr(j))-taxprop(iHFlast,1)-
     1                     deprINV0)*RCavgrent(1,iHF)+
     1  PH(2)*BeqInd(j,5)*
     1   (1.0-deprH(2)*DeprGrid(iDepr(j))-taxprop(iHFlast,2)-
     1                     deprINV0)*RCavgrent(2,iHF)
       end if
       if(NWind(i).lt.NWmin) NWind(i)=NWmin
      end do





!need to redo below separately for 3 groups: RClast=1,2,3
!might need to compute number of each type ahead of time
!make code modular so that if there are no agents in group 2 or 3 (as will happen when nRClast=1) then there is no problem
!Computing who receives rent control based on RCprob. However, RCprob is updated each iteration so that the total size of rent controlled units demanded is equal to the amount supplied
      tempI1=nint(RCprob(1)*
     1 (real(nAgent)-nAgentRClast(1)-nAgentRClast(2)))
      tempI2=nint((RCprob(1)+RCprob(2))*
     1 (real(nAgent)-nAgentRClast(1)-nAgentRClast(2)))
      if(nRClast.eq.1) then
       tempI3=nint(RCprobTemp(1,1)*real(nAgentRClast(1)))
       tempI4=nint((RCprobTemp(1,1)+RCprobTemp(2,1))*
     1             real(nAgentRClast(1)))
       tempI5=nint(RCprobTemp(1,1)*real(nAgentRClast(2)))
       tempI6=nint((RCprobTemp(1,1)+RCprobTemp(2,1))*
     1             real(nAgentRClast(2)))
      else
       tempI3=nint(RCprobTemp(1,2)*real(nAgentRClast(1)))
       tempI4=nint((RCprobTemp(1,2)+RCprobTemp(2,2))*
     1             real(nAgentRClast(1)))
       tempI5=nint(RCprobTemp(1,3)*real(nAgentRClast(2)))
       tempI6=nint((RCprobTemp(1,3)+RCprobTemp(2,3))*
     1             real(nAgentRClast(2)))
      end if
      if(tempI1.gt.nAgent-nAgentRClast(1)-nAgentRClast(2))
     1 tempI1=nAgent-nAgentRClast(1)-nAgentRClast(2)
      if(tempI2.gt.nAgent-nAgentRClast(1)-nAgentRClast(2))
     1 tempI2=nAgent-nAgentRClast(1)-nAgentRClast(2)
      if(tempI3.gt.nAgentRClast(1)) tempI3=nAgentRClast(1)
      if(tempI4.gt.nAgentRClast(1)) tempI4=nAgentRClast(1)
      if(tempI5.gt.nAgentRClast(2)) tempI5=nAgentRClast(2)
      if(tempI6.gt.nAgentRClast(2)) tempI6=nAgentRClast(2)

      if(tempI1.ne.RCreceivercut(1).or.tempI2.ne.RCreceivercut(2)) then

c$omp parallel
c$omp& default(none)
c$omp& shared(i,nAgent,RCreceiver,nRC,nAgentRClast,RClastInd,nRClast,
c$omp& RCshock,RCshock0,RCshock1,RCshock2,tempI1,tempI2,tempI3,tempI4,
c$omp& tempI5,tempI6)
c$omp do
      do i=1,nAgent
       RCreceiver(i)=0
!new agents (RClastInd(i)=1) receiving RC
       if(nRC.eq.1.and.tempI2.gt.0.and.RClastInd(i).eq.1) then
        if(tempI1.gt.0) then !tempI1>0 --> at least someone receives RC in z1
         if(RCshock(i).le.RCshock0(tempI1)) RCreceiver(i)=1
         if(RCshock(i).gt.RCshock0(tempI1).and.
     1      RCshock(i).le.RCshock0(tempI2)) RCreceiver(i)=2
        else                !tempI1=0 & tempI2>0 --> noone receives RC in z1, but at least someone in z2
         if(RCshock(i).le.RCshock0(tempI2)) RCreceiver(i)=2
        end if
       end if
!agents already in RC in z1
       if(nRC.eq.1.and.nAgentRClast(1).gt.0.and.
     1    RClastInd(i).eq.2.and.tempI4.gt.0) then
        if(tempI3.gt.0) then !tempI3>0 --> at least someone receives RC in z1
         if(RCshock(i).le.RCshock1(tempI3)) RCreceiver(i)=1
         if(RCshock(i).gt.RCshock1(tempI3).and.
     1      RCshock(i).le.RCshock1(tempI4)) RCreceiver(i)=2
        else  !tempI3=0 & tempI4>0 --> noone receives RC in z1, but at least someone in z2
         if(RCshock(i).le.RCshock1(tempI4)) RCreceiver(i)=2
        end if
       end if
!agents already in RC in z2
       if(nRC.eq.1.and.nAgentRClast(2).gt.0.and.
     1    RClastInd(i).eq.3.and.tempI6.gt.0) then
        if(tempI5.gt.0) then !tempI5>0 --> at least someone receives RC in z1
         if(RCshock(i).le.RCshock2(tempI5)) RCreceiver(i)=1
         if(RCshock(i).gt.RCshock2(tempI5).and.
     1      RCshock(i).le.RCshock2(tempI6)) RCreceiver(i)=2
        else  !tempI5=0 & tempI6>0 --> noone receives RC in z1, but at least someone in z2
         if(RCshock(i).le.RCshock2(tempI6)) RCreceiver(i)=2
        end if
       end if
       if(tempI1.eq.0.and.tempI2.eq.0.and.tempI3.eq.0.and.tempI4.eq.0)
     1    RCreceiver(i)=0
      end do
c$omp end do
c$omp end parallel

      end if

      RCreceivercut(1)=tempI1
      RCreceivercut(2)=tempI2

      call getpolicy0(policy,dPolicyNW,dValFunNW,ValFunCond,PensionGrid,
     1     nDZ,nRClast,nAge,nAgent,nAgg,nInd,nWage,
     1     nRent1,nRent2,nRP1,nRP2,nH1,nH2,nNW,nHF,nLOC,nRC,NWgridAll,
     1     WageGrid,Rent1grid,Rent2grid,RP1grid,RP2grid,H1grid,H2grid,
     1     Wage,Rent1,Rent2,RP1,RP2,H1last/real(nAgent),
     1     H2last/real(nAgent),iHF,
     1     AgeInd,iZind,NWind,Zind,Cind,Hind,LOCind,RenterInd,
     1     RClastInd,ValFunInd,
     1     PensionBelief,TieBreaker,RCreceiver,t,iClMkt,gamma0,alphaN)

c$omp parallel
c$omp& default(none)
c$omp& shared(t,nAge,nAgent,nRet,i,alphaN,alphaC,alphaH,deprH,deprINV0,
c$omp& PH,AgeProd,CommCost,Pension,taxss,AgeInd,LOCind,HoursInd,Cind,
c$omp& Hind,RenterInd,HresInd,Wage,Rent,iClMkt,Zind,LeisureMin,iHF,
c$omp& HresMin,taxprop,CluxCut,CluxCost,flagRetInd,RCinccut,RCrentred,
c$omp& RChsize,ElastCH,ElastCN,param1,param2,NWind,RCavgRent,Profit,
c$omp& thetaRes,thetaInv,chi0,HoursMin,HoursConst2,lambda0,tau0,r0,
c$omp& lambdaBase,tauBase,RClastInd)
c$omp& private(tempR1,tempR2,tempR3,tempR4,HoursConst0,HoursConst1,
c$omp& HouseConst0,HouseConst1,HouseConst2,HoursConst3,HoursGrid,
c$omp& iHoursChoice,TaxableIncome,HSVtax,HSVtaxBase,HresMinVoucher)
c$omp do

      do i=1,nAgent

       HoursConst3=Zind(i)*Wage*AgeProd(AgeInd(i))*
     1             HoursConst2(LOCind(i),RenterInd(i))*
     1            (1.0-alphaN)*(1.0-alphaH)/(chi0*alphaN)
       HouseConst0=(alphaH/(alphaC*Rent(LOCind(i))))
       HouseConst1=HouseConst0/(1.0-RCrentred(LOCind(i),iHF))
       HouseConst2=HouseConst0*
     1   (1.0-deprH(LOCind(i))-taxProp(iHF,LOCind(i))-deprINV0)/
     1   (1.0-deprH(LOCind(i))-taxProp(iHF,LOCind(i))-
     1   deprINV0*PH(LOCind(i))/Rent(LOCind(i)))

!!Old way of computing hours - works only if HSV tax is zeor
!       HoursConst0=((1.0-taxss)*Zind(i)*
!     1              Wage*AgeProd(AgeInd(i)))**(-1.0/(1.0-chi0*ElastCN))
!       if(abs(ElastCH).gt.0.0001) then
!        HoursConst1=(alphaC+alphaH*
!     1  ((alphaH/(alphaC*Rent(LOCind(i))))**(ElastCH/(1.0-ElastCH))))**
!     1  ((ElastCH-ElastCN)/(ElastCH*(1.0-chi0*ElastCN)))
!       else
!        HoursConst1=(alphaC*Rent(LOCind(i))/alphaH)**
!     1              (alphaH*ElastCN/(1.0-chi0*ElastCN))
!       end if
!       HoursInd(i)=1.0-LeisureMin-CommCost(LOCind(i),flagRetInd(i))-
!     1             (Cind(i)**param2)*param1*HoursConst0*HoursConst1
!       if(LOCind(i).eq.2.and.Cind(i).gt.CluxCut(flagRetInd(i))) then
!        HoursInd(i)=1.0-LeisureMin-CommCost(LOCind(i),flagRetInd(i))-
!     1              (Cind(i)**param2)*param1*HoursConst0*HoursConst1*
!     1             (1.0+CluxCost(flagRetInd(i)))
!       end if
!!new way of computing hours, works for HSV tax. searches for solution of non-linear equation relating C and H
       tempR1=0.0 !hours guess
       tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1   ((r0*NWind(i)+Profit+tempR1*
     1     Zind(i)*Wage*AgeProd(AgeInd(i)))**(-tau0(iHF)))
       tempR3=(1.0-LeisureMin-CommCost(LOCind(i),flagRetInd(i))-
     1         tempR1)**(chi0*elastCN-1.0)
       HoursGrid(1,1)=tempR1
       HoursGrid(1,2)=(HoursConst3*tempR2/tempR3)**(1.0/(1.0-elastCN))  !consumption given hours guess
       tempR1=0.5 !hours guess
       tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1   ((r0*NWind(i)+Profit+tempR1*
     1     Zind(i)*Wage*AgeProd(AgeInd(i)))**(-tau0(iHF)))
       tempR3=(1.0-LeisureMin-CommCost(LOCind(i),flagRetInd(i))-
     1         tempR1)**(chi0*elastCN-1.0)
       HoursGrid(2,1)=tempR1
       HoursGrid(2,2)=(HoursConst3*tempR2/tempR3)**(1.0/(1.0-elastCN))  !consumption given hours guess
       tempR1=1.0-LeisureMin-CommCost(LOCind(i),flagRetInd(i))-0.01 !hours guess
       tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1   ((r0*NWind(i)+Profit+tempR1*
     1     Zind(i)*Wage*AgeProd(AgeInd(i)))**(-tau0(iHF)))
       tempR3=(1.0-LeisureMin-CommCost(LOCind(i),flagRetInd(i))-
     1         tempR1)**(chi0*elastCN-1.0)
       HoursGrid(3,1)=tempR1
       HoursGrid(3,2)=(HoursConst3*tempR2/tempR3)**(1.0/(1.0-elastCN))  !consumption given hours guess
       do iHoursChoice=1,7
        if(abs(Cind(i)-0.5*(HoursGrid(1,2)+HoursGrid(2,2))).lt.
     1     abs(Cind(i)-0.5*(HoursGrid(2,2)+HoursGrid(3,2)))) then
         HoursGrid(3,1)=HoursGrid(2,1)
         HoursGrid(3,2)=HoursGrid(2,2)
         HoursGrid(2,1)=0.5*(HoursGrid(1,1)+HoursGrid(2,1))
        else
         HoursGrid(1,1)=HoursGrid(2,1)
         HoursGrid(1,2)=HoursGrid(2,2)
         HoursGrid(2,1)=0.5*(HoursGrid(2,1)+HoursGrid(3,1))
        end if
        tempR1=HoursGrid(2,1)
        tempR2=-taxss+(1.0-tau0(iHF))*lambda0(iHF)*
     1   ((r0*NWind(i)+Profit+tempR1*
     1     Zind(i)*Wage*AgeProd(AgeInd(i)))**(-tau0(iHF)))
        tempR3=(1.0-LeisureMin-CommCost(LOCind(i),flagRetInd(i))-
     1         tempR1)**(chi0*elastCN-1.0)
        HoursGrid(2,2)=(HoursConst3*tempR2/tempR3)**(1.0/(1.0-elastCN))
       end do
       if(abs(Cind(i)-0.5*(HoursGrid(1,2)+HoursGrid(2,2))).lt.
     1    abs(Cind(i)-0.5*(HoursGrid(2,2)+HoursGrid(3,2)))) then
        tempR1=(Cind(i)-HoursGrid(1,2))/(HoursGrid(2,2)-HoursGrid(1,2))
        HoursInd(i)=HoursGrid(1,1)+tempR1*
     1             (HoursGrid(2,1)-HoursGrid(1,1))
       else
        tempR1=(Cind(i)-HoursGrid(2,2))/(HoursGrid(3,2)-HoursGrid(2,2))
        HoursInd(i)=HoursGrid(2,1)+tempR1*
     1             (HoursGrid(3,1)-HoursGrid(2,1))
       end if
!end of new way of computing hours
       if(HoursInd(i).lt.HoursMin.and.AgeInd(i).le.nAge-nRet)
     1  HoursInd(i)=HoursMin
       if(RenterInd(i).eq.3.and.AgeInd(i).le.nAge-nRet.and.
     1    RClastInd(i).eq.1.and.
     1    RCinccut(LOCind(i),iHF).lt.
     1    HoursInd(i)*Wage*Zind(i)*AgeProd(AgeInd(i))) then
        HoursInd(i)=RCinccut(LOCind(i),iHF)/
     1             (Wage*Zind(i)*AgeProd(AgeInd(i)))
       end if
       if(HoursInd(i).lt.0.0) HoursInd(i)=0.0

       TaxableIncome=r0*NWind(i)+Profit+
     1               HoursInd(i)*Zind(i)*Wage*AgeProd(AgeInd(i))
       HSVtax=TaxableIncome-
     1        lambda0(iHF)*(TaxableIncome**(1.0-tau0(iHF)))
       HSVtaxBase=TaxableIncome-
     1            lambdaBase*(TaxableIncome**(1.0-tauBase))
       if(HSVtax.lt.0.and.HSVtax.lt.HSVtaxBase) then
        HresMinVoucher=(HSVtaxBase-HSVtax)/Rent(LOCind(i))
       else
        HresMinVoucher=0.0
       end if

       if(RenterInd(i).eq.1.or.RenterInd(i).eq.3) then
        if(RenterInd(i).eq.1) then
         HresInd(i)=Cind(i)*(HouseConst0**(1.0/(1.0-ElastCH)))
         if(HresInd(i).lt.HresMin) HresInd(i)=HresMin !impose min housing size constraint
         if(HresInd(i).lt.HresMinVoucher) HresInd(i)=HresMinVoucher
        else
         HresInd(i)=Cind(i)*(HouseConst1**(1.0/(1.0-ElastCH)))
         if(HresInd(i).lt.HresMin) HresInd(i)=HresMin !impose min housing size constraint
         if(HresInd(i).lt.HresMinVoucher) HresInd(i)=HresMinVoucher
         tempR1=RChsize(LOCind(i),iHF)/
     1         (Rent(LOCind(i))*(1.0-RCrentred(LOCind(i),iHF)))
         if(HresInd(i).gt.tempR1) then
          HresInd(i)=tempR1
          if(HresInd(i).lt.HresMin) HresInd(i)=HresMin !impose min housing size constraint
          if(HresInd(i).lt.HresMinVoucher) HresInd(i)=HresMinVoucher
         end if
        end if
       else
        HresInd(i)=Cind(i)*(HouseConst2**(1.0/(1.0-ElastCH)))
        if(HresInd(i).lt.HresMin) HresInd(i)=HresMin !impose min housing size constraint
        if(HresInd(i).lt.HresMinVoucher) HresInd(i)=HresMinVoucher
       end if
       if(LOCind(i).eq.2.and.Cind(i).gt.CluxCut(flagRetInd(i))) then
        HresInd(i)=HresInd(i)*(1.0+CluxCost(flagRetInd(i)))
        tempR1=RChsize(LOCind(i),iHF)/
     1    (Rent(LOCind(i))*(1.0-RCrentred(LOCind(i),iHF)))
        if (RenterInd(i).eq.3.and.HresInd(i).gt.tempR1) then
         HresInd(i)=tempR1
         if(HresInd(i).lt.HresMin) HresInd(i)=HresMin !impose min housing size constraint
         if(HresInd(i).lt.HresMinVoucher) HresInd(i)=HresMinVoucher
        end if
       end if

       if(RenterInd(i).eq.2) then
        tempR3=NWind(i)-PH(LOCind(i))*RCavgrent(LOCind(i),iHF)*Hind(i)-
     1         PH(LOCind(i))*HresInd(i)
        if(tempR3.lt.-PH(LOCind(i))*(thetaRes*HresInd(i)+
     1                thetaInv*RCavgrent(LOCind(i),iHF)*Hind(i))) then
         tempR1=PH(LOCind(i))*(1.0-thetaInv)*RCavgrent(LOCind(i),iHF)
         tempR2=PH(LOCind(i))*(1.0-thetaRes)
         HresInd(i)=(NWind(i)-Hind(i)*tempR1)/tempR2
         if(HresInd(i).lt.HresMin*1.001.or.
     1      HresInd(i).lt.HresMinVoucher+0.001) then
          Hind(i)=0.0
          HresInd(i)=NWind(i)/tempR2
          if(HresInd(i).lt.HresMin) HresInd(i)=HresMin
         end if
        end if
       end if


!       if(AgeInd(i).gt.nAge-nRet) then
!        HoursInd(i)=1.0-LeisureMin-CommCost(LOCind(i),2)-
!     1              Cind(i)*(alphaN/(alphaC*(1.0-alphaN)))*
!     1             (1.0/((1.0-taxss)*Wage*Zind(i)*AgeProd(AgeInd(i))))
!        if(LOCind(i).eq.2.and.Cind(i).gt.CluxCut(flagRetInd(i))) then
!         HoursInd(i)=1.0-LeisureMin-CommCost(LOCind(i),2)-
!     1              Cind(i)*(alphaN/(alphaC*(1.0-alphaN)))*
!     1             (1.0/((1.0-taxss)*Wage*Zind(i)*AgeProd(AgeInd(i))))*
!     1              (1.0+CluxCost(flagRetInd(i)))
!        end if
!       else
!        HoursInd(i)=1.0-LeisureMin-CommCost(LOCind(i),1)-
!     1              Cind(i)*(alphaN/(alphaC*(1.0-alphaN)))*
!     1             (1.0/((1.0-taxss)*Wage*Zind(i)*AgeProd(AgeInd(i))))
!        if(LOCind(i).eq.2.and.Cind(i).gt.CluxCut(flagRetInd(i))) then
!         HoursInd(i)=1.0-LeisureMin-CommCost(LOCind(i),1)-
!     1              Cind(i)*(alphaN/(alphaC*(1.0-alphaN)))*
!     1             (1.0/((1.0-taxss)*Wage*Zind(i)*AgeProd(AgeInd(i))))*
!     1              (1.0+CluxCost(flagRetInd(i)))
!        end if
!        if(RenterInd(i).eq.3.and.RCinccut(LOCind(i),iHF).lt.
!     1     HoursInd(i)*Wage*Zind(i)*AgeProd(AgeInd(i))) then
!         HoursInd(i)=RCinccut(LOCind(i),iHF)/
!     1              (Wage*Zind(i)*AgeProd(AgeInd(i)))
!        end if
!       end if
!       !if(HoursInd(i).lt.0.0.or.AgeInd(i).gt.nAge-nRet) HoursInd(i)=0.0
!       if(HoursInd(i).lt.0.0) HoursInd(i)=0.0
!       if(RenterInd(i).eq.1.or.RenterInd(i).eq.3) then
!        if(RenterInd(i).eq.1) then
!         HresInd(i)=(alphaH/alphaC)*Cind(i)/Rent(LOCind(i))
!        else
!         HresInd(i)=(alphaH/alphaC)*Cind(i)/
!     1              (Rent(LOCind(i))*(1.0-RCrentred(LOCind(i),iHF)))
!         tempR1=RChsize(LOCind(i),iHF)/
!     1         (Rent(LOCind(i))*(1.0-RCrentred(LOCind(i),iHF)))
!         if(HresInd(i).gt.tempR1) HresInd(i)=tempR1
!        end if
!       else
!        HresInd(i)=(alphaH/alphaC)*(1.0/Rent(LOCind(i)))*Cind(i)*
!     1       (1.0-deprH(LOCind(i))-taxProp(iHF)-deprINV0)/
!     1       (1.0-deprH(LOCind(i))-taxProp(iHF)-deprINV0*PH(LOCind(i))/
!     1        Rent(LOCind(i)))
!       end if
!       if(LOCind(i).eq.2.and.Cind(i).gt.CluxCut(flagRetInd(i))) then
!        HresInd(i)=HresInd(i)*(1.0+CluxCost(flagRetInd(i)))
!       end if
!       if(HresInd(i).lt.HresMin) HresInd(i)=HresMin
      end do

c$omp end do
c$omp end parallel

      PensionTax=0.0
      Hres(1)=0.0
      Hres(2)=0.0
      HresRenter(1)=0.0
      HresRenter(2)=0.0
      HresOwner(1)=0.0
      HresOwner(2)=0.0
      HresRC(1)=0.0
      HresRC(2)=0.0
      Hinv(1)=0.0
      Hinv(2)=0.0
      Cons=0.0
      Hours=0.0

!Do not parallelize this loop because Hours, Cons, Hres, PensionTax are being incremented
      do i=1,nAgent
       !if(AgeInd(i).le.nAge-nRet) then
       if(HoursInd(i).gt.0.00001) then
        PensionTax=PensionTax+
     1             HoursInd(i)*Wage*Zind(i)*AgeProd(AgeInd(i))*taxss
       end if
       if(RenterInd(i).eq.1.or.RenterInd(i).eq.3) then
        HresRenter(LOCind(i))=HresRenter(LOCind(i))+HresInd(i)
        if(RenterInd(i).eq.3) then
         HresRC(LOCind(i))=HresRC(LOCind(i))+HresInd(i)
        end if
       else
        HresOwner(LOCind(i))=HresOwner(LOCind(i))+HresInd(i)
       end if
       Cons=Cons+Cind(i)
       Hours=Hours+HoursInd(i)*Zind(i)*AgeProd(AgeInd(i))
       Hres(LOCind(i))=Hres(LOCind(i))+HresInd(i)
       Hinv(LOCind(i))=Hinv(LOCind(i))+Hind(i)
      end do

!This is the ratio of average price to market price. It accounts for owners (who pay market), market investors (who pay market), and stabilized investors (who pay RCrenred x market)
      if(Hres(1).gt.0) then
       PHavgMult(1)=(HresOwner(1)+(Hres(1)-HresOwner(1))*
     1              RCavgrentDev(1,iHF))/Hres(1)
      else
       PHavgMult(1)=1.0
      end if
      if(Hres(2).gt.0) then
       PHavgMult(2)=(HresOwner(2)+(Hres(2)-HresOwner(2))*
     1              RCavgrentDev(2,iHF))/Hres(2)
      else
       PHavgMult(2)=1.0
      end if

      if(NumRetired.gt.0) then
       Pension=PensionBelief!PensionTax/real(NumRetired)
      else
       Pension=0.0
      end if

      if(iClMkt.eq.iClMktBreak.or.iClMkt.eq.nClMkt) then

c$omp parallel
c$omp& default(none)
c$omp& shared(nAge,nAgent,nRet,i,t,AgeInd,LaborIncomeInd,HoursInd,Zind,
c$omp& AgeProd,taxss,Wage,Pension,SSIdist,iZind,CommCostFin,LOCind,
c$omp& iHF,iClMkt,RCinccut,RenterInd,RClastInd)
c$omp& private(tempR1)
c$omp do
      do i=1,nAgent
       if(AgeInd(i).gt.nAge-nRet) then
        LaborIncomeInd(i)=HoursInd(i)*Wage*
     1                    Zind(i)*AgeProd(AgeInd(i))*(1.0-taxss)+
     1                    SSIdist(iZind(i))*Pension-
     1                    CommCostFin(LOCind(i),2)!PensionBelief
        if(RenterInd(i).eq.3.and.RClastInd(i).eq.1.and.
     1     SSIdist(iZind(i))*Pension.gt.RCinccut(LOCind(i),iHF)) then
         LaborIncomeInd(i)=RCinccut(LOCind(i),iHF)-
     1    CommCostFin(LOCind(i),2)
        end if
       else
        tempR1=CommCostFin(LOCind(i),1)
        if(HoursInd(i).lt.0.00001) tempR1=CommCostFin(LOCind(i),2)
        LaborIncomeInd(i)=HoursInd(i)*Wage*
     1                    Zind(i)*AgeProd(AgeInd(i))*(1.0-taxss)-
     1                    tempR1
       end if
      end do
c$omp end do
c$omp end parallel

      end if

      PHavg(1)=PH(1)*PHavgMult(1)
      PHavg(2)=PH(2)*PHavgMult(2)
      ForDemTot(1)=exp(HFgrid0(iHF,1)-
     1                 HFgrid1(iHF,1)*log(PH(1)*(1.0+taxpropOOT(1))))
      ForDemTot(2)=exp(HFgrid0(iHF,2)-
     1                 HFgrid1(iHF,2)*log(PH(2)*(1.0+taxpropOOT(2))))
      Hdem(1)=(Hres(1)/real(nAgent))+ForDemTot(1)*HFVgrid(iHF,1)
      Hdem(2)=(Hres(2)/real(nAgent))+ForDemTot(2)*HFVgrid(iHF,2)
      tempR1=1.0-(Hdem(1)/HBARloc1(iHF))
      tempR2=1.0-(Hdem(2)/HBARloc2(iHF))
      if(tempR1.lt.0.0001) tempR1=0.0001
      if(tempR2.lt.0.0001) tempR2=0.0001
      HoursDemandC=nFirmC*(RTSC/Wage)**(1.0/(1.0-RTSC))
      if(abs(RTSH0loc1-1.0).gt.0.0001) then
       HoursDemandLOC1=nFirm1*
     1           (tempR1*RTSH0loc1*PHavg(1)/Wage)**(1.0/(1.0-RTSH0loc1))
      else
       tempR3=Hdem(1)*real(nAgent)-(1.0-deprH(1))*H1last
       HoursDemandLOC1=(tempR3/tempR1)+
     1                 (PHavg(1)-Wage/tempR1)*real(nAgent)*HBARloc1(iHF)
      end if
      if(abs(RTSH0loc2-1.0).gt.0.0001) then
       HoursDemandLOC2=nFirm2*
     1           (tempR2*RTSH0loc2*PHavg(2)/Wage)**(1.0/(1.0-RTSH0loc2))
      else
       tempR4=Hdem(2)*real(nAgent)-(1.0-deprH(2))*H2last
       HoursDemandLOC2=(tempR4/tempR2)+
     1                 (PHavg(2)-Wage/tempR2)*real(nAgent)*HBARloc2(iHF)
      end if
      if(HoursDemandLOC1.lt.0.0001) HoursDemandLOC1=0.0001
      if(HoursDemandLOC2.lt.0.0001) HoursDemandLOC2=0.0001
      HoursDemand=HoursDemandC+HoursDemandLOC1+HoursDemandLOC2
      H1=(1.0-deprH(1))*H1last+nFirm1*tempR1*
     1  ((HoursDemandLOC1/nFirm1)**RTSH0loc1)
      if(HoursDemandLOC1.lt.0.0001) H1=(1.0-deprH(1))*H1last !this is done because fortran thinks 0**0=1
      H2=(1.0-deprH(2))*H2last+nFirm2*tempR2*
     1  ((HoursDemandLOC2/nFirm2)**RTSH0loc2)
      if(HoursDemandLOC2.lt.0.0001) H2=(1.0-deprH(2))*H2last !this is done because fortran thinks 0**0=1
      ProfitC=nFirmC*(((HoursDemandC/nFirmC)**RTSC)-
     1                 (HoursDemandC/nFirmC)*Wage)
      ProfitLOC1=nFirm1*(
     1           PHavg(1)*tempR1*((HoursDemandLOC1/nFirm1)**RTSH0loc1)-
     1          (HoursDemandLOC1/nFirm1)*Wage)
      ProfitLOC2=nFirm2*(
     1           PHavg(2)*tempR2*((HoursDemandLOC2/nFirm2)**RTSH0loc2)-
     1          (HoursDemandLOC2/nFirm2)*Wage)
      Profit=(ProfitC*ProfitRedist(1)+ProfitLOC1*ProfitRedist(2)+
     1        ProfitLOC2*ProfitRedist(3))/real(nAgent)

      do i=1,24
       do j=1,7
        err(26-i,j)=err(25-i,j)
       end do
      end do
      err(1,1)=HoursDemand-Hours
      err(1,2)=Hdem(1)*real(nAgent)-H1  !zone 1: LocalDemand + ForeignDemand*Vacant - Supply --> foreigners are only taking up housing if they leave them vacant
      err(1,3)=Hdem(2)*real(nAgent)-H2  !zone 2: LocalDemand + ForeignDemand*Vacant - Supply --> foreigners are only taking up housing if they leave them vacant
      err(1,4)=HresRenter(1)-Hinv(1)-
     1        (1.0-HFVgrid(iHF,1))*ForDemTot(1)*real(nAgent)        !zone 1: LocalRentalDemand - LocalInvestmentProperty - ForeignInvestmentProperty  --> ForeignInvestmentProperty=ForeignDemand*(1-Vacant)
      err(1,5)=HresRenter(2)-Hinv(2)-
     1        (1.0-HFVgrid(iHF,2))*ForDemTot(2)*real(nAgent)        !zone 1: LocalRentalDemand - LocalInvestmentProperty - ForeignInvestmentProperty  --> ForeignInvestmentProperty=ForeignDemand*(1-Vacant)
      err(1,6)=RCshare(1,iHF)*Hinv(1)-HresRC(1)
      err(1,7)=RCshare(2,iHF)*Hinv(2)-HresRC(2)
      errNorm(1,1)=0.5*(HoursDemand+Hours)
      if(errNorm(1,1).lt.0.01*real(nAgent)) then
       errNorm(1,1)=0.01*real(nAgent)
      end if
      errNorm(1,2)=0.5*(H1+Hdem(1)*real(nAgent))
      if(errNorm(1,2).lt.0.01*real(nAgent)) then
       errNorm(1,2)=0.01*real(nAgent)
      end if
      errNorm(1,3)=0.5*(H2+Hdem(2)*real(nAgent))
      if(errNorm(1,3).lt.0.01*real(nAgent)) then
       errNorm(1,3)=0.01*real(nAgent)
      end if
      errNorm(1,4)=errNorm(1,2)
      errNorm(1,5)=errNorm(1,3)
      if(RCshare(1,iHF)*Hinv(1).gt.0.0001) then
       errNorm(1,6)=RCshare(1,iHF)*Hinv(1)
      else
       errNorm(1,6)=1.0
      end if
      if(RCshare(2,iHF)*Hinv(2).gt.0.0001) then
       errNorm(1,7)=RCshare(2,iHF)*Hinv(2)
      else
       errNorm(1,7)=1.0
      end if
      tempR1=abs(err(1,1)/errNorm(1,1))+
     1       abs(err(1,2)/errNorm(1,2))+
     1       abs(err(1,3)/errNorm(1,3))+
     1       abs(err(1,4)/errNorm(1,4))+
     1       abs(err(1,5)/errNorm(1,5))+
     1       abs(err(1,6)/errNorm(1,6))+
     1       abs(err(1,7)/errNorm(1,7))
      if(errBest.gt.tempR1) then
       errBest=tempR1
       WageBest=Wage
       Rent1best=Rent1
       Rent2best=Rent2
       RP1best=RP1
       RP2best=RP2
       RCprobBest(1)=RCprob(1)
       RCprobBest(2)=RCprob(2)
      end if
      if(iClMkt.gt.15) then
       do j=1,5
        CountNeg(j)=0
        do i=1,15
         if(err(i,j).lt.0) CountNeg(j)=CountNeg(j)+1
        end do

        if(CountNeg(j).le.0.or.CountNeg(j).ge.15) then
         upd(j)=upd(j)*1.01
        else
         upd(j)=upd(j)/1.01
        end if
!        tempI1=1
!        if(iClMkt.gt.500) tempI1=50
!        if(mod(iClMkt,tempI1).eq.0) then
!         if(CountNeg(j).le.0.or.CountNeg(j).ge.25) then
!          upd(j)=upd(j)*1.5
!         else
!          upd(j)=upd(j)/1.5
!         end if
!        end if
       end do
      end if
      if(upd(1).gt.0.2) upd(1)=0.2
      if(upd(1).lt.0.0001) upd(1)=0.0001
      if(upd(2).gt.0.05) upd(2)=0.05
      if(upd(2).lt.0.000001) upd(2)=0.0000005
      if(upd(3).gt.0.05) upd(3)=0.05
      if(upd(3).lt.0.000001) upd(3)=0.0000005
      if(upd(4).gt.0.005) upd(4)=0.005
      if(upd(4).lt.0.000001) upd(4)=0.0000005
      if(upd(5).gt.0.005) upd(5)=0.005
      if(upd(5).lt.0.000001) upd(5)=0.0000005

!MARKET CLEARING need to find prices (Wage,Rent1,Rent2,RP1,RP2) s.t.
!Hours=HoursDemand
!Hres(1)=H1
!Hres(2)=H2
!Hinv(1)=HresRenter(1)
!Hinv(2)=HresRenter(2)
!      if(t.eq.13.and.iHF.eq.1.and.
!     1   (iClMkt.le.20.or.mod(iClMkt,1).eq.0)) then
!
!      if(iClMkt.eq.1.or.iClMkt.eq.2) then
!       if(t.eq.41) then
!       do i=1,nAgent
!       write(6,'(i5,i4,i3,f8.4,f8.4,i3,i3,f8.4,f8.4)')
!     1 i,AgeInd(i),iZind(i),NWind(i),Cind(i),RenterInd(i),LOCind(i),
!     1 HresInd(i),Hind(i)
!       end do
!       end if
!      end if
!      write(6,'(i6,i6,f11.7,f11.7,f11.7,f11.7,f11.7,f8.4,f8.4,f8.4,f8.4,
!     1 f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4)')
!     1 t,iClMkt,Wage,Rent(1),Rent(2),RP1,RP2,Hours/real(nAgent),
!     1 HoursDemand/real(nAgent),
!     1 Hdem(1),H1/real(nAgent),
!     1 Hdem(2),H2/real(nAgent),
!     1 HresRenter(1)/real(nAgent),
!     1 (1.0-HFVgrid(iHF,1))*ForDemTot(1)+Hinv(1)/real(nAgent),
!     1 HresRenter(2)/real(nAgent),
!     1 (1.0-HFVgrid(iHF,2))*ForDemTot(2)+Hinv(2)/real(nAgent),
!     1 HresRC(1)/real(nAgent),RCshare(1,iHF)*Hinv(1)/real(nAgent),
!     1 HresRC(2)/real(nAgent),RCshare(2,iHF)*Hinv(2)/real(nAgent),
!     1 RCprob(1),RCprob(2)
!      end if

      tempR2=err(1,2)
      tempR3=err(1,3)
      if(err(1,2)+err(1,3).gt.0) then
       if(err(1,2).lt.0) tempR2=0.0
       if(err(1,3).lt.0) tempR3=0.0
      else
       if(err(1,2).gt.0) tempR2=0.0
       if(err(1,3).gt.0) tempR3=0.0
      end if

      Wage=Wage+upd(1)*err(1,1)/errNorm(1,1)!real(nAgent)
      !Rent1=Rent1*(1.0+upd(2)*tempR2/real(nAgent))
      !Rent2=Rent2*(1.0+upd(3)*tempR3/real(nAgent))
      Rent1=Rent1+upd(2)*tempR2/real(nAgent)
      Rent2=Rent2+upd(3)*tempR3/real(nAgent)
      RP1=RP1+upd(4)*err(1,4)/errNorm(1,4)!real(nAgent)
      RP2=RP2+upd(5)*err(1,5)/errNorm(1,5)!real(nAgent)

      RCprob(1)=RCprob(1)+0.1*(RCshare(1,iHF)*Hinv(1)-HresRC(1))/H1last
      RCprob(2)=RCprob(2)+0.1*(RCshare(2,iHF)*Hinv(2)-HresRC(2))/H2last
      if(RCprob(1).lt.0.0) RCprob(1)=0.0
      if(RCprob(2).lt.0.0) RCprob(2)=0.0
      if(RCprob(1).gt.1.0) RCprob(1)=1.0
      if(RCprob(2).gt.1.0) RCprob(2)=1.0
      do i=1,nRClast
       if (i.eq.1.or.flagRCstay(iHF).eq.0) then
        RCprobTemp(1,i)=RCprob(1)
        RCprobTemp(2,i)=RCprob(2)
       else
        if(i.eq.2) then
         RCprobTemp(1,i)=RCprobStay(1)
         RCprobTemp(2,i)=0.0
         if(RCprobTemp(1,i).lt.RCprob(1)) RCprobTemp(1,i)=RCprob(1)
        end if
        if(i.eq.3) then
         RCprobTemp(1,i)=0.0
         RCprobTemp(2,i)=RCprobStay(2)
         if(RCprobTemp(2,i).lt.RCprob(2)) RCprobTemp(2,i)=RCprob(2)
        end if
       end if
      end do

      if(Wage.lt.WageGrid(1)) Wage=WageGrid(1)
      if(Wage.gt.WageGrid(nWage)) Wage=WageGrid(nWage)
      if(Rent1.lt.Rent1Grid(1)) Rent1=Rent1Grid(1)
      if(Rent1.gt.Rent1Grid(nRent1)) Rent1=Rent1Grid(nRent1)
      if(Rent2.lt.Rent2Grid(1)) Rent2=Rent2Grid(1)
      if(Rent2.gt.Rent2Grid(nRent2)) Rent2=Rent2Grid(nRent2)
      if(RP1.lt.RP1Grid(1)) RP1=RP1Grid(1)
      if(RP1.gt.RP1Grid(nRP1)) RP1=RP1Grid(nRP1)
      if(RP2.lt.RP2Grid(1)) RP2=RP2Grid(1)
      if(RP2.gt.RP2Grid(nRP2)) RP2=RP2Grid(nRP2)

      tempR1=0.5*(HresRenter(1)+Hinv(1)+
     1            (1.0-HFVgrid(iHF,1))*ForDemTot(1)*real(nAgent))
      tempR2=0.5*(HresRenter(2)+Hinv(2)+
     1            (1.0-HFVgrid(iHF,2))*ForDemTot(2)*real(nAgent))
      if(tempR1.lt.0.01*real(nAgent)) tempR1=0.01*real(nAgent)
      if(tempR2.lt.0.01*real(nAgent)) tempR2=0.01*real(nAgent)
!      tempR3=0.5*(Hdem(1)*real(nAgent)+H1)
!      tempR4=0.5*(Hdem(2)*real(nAgent)+H2)
!      tempR5=0.5*(HoursDemand+Hours)
      if(tempR1.lt.0.01) tempR1=0.01
      if(tempR2.lt.0.01) tempR2=0.01
      if(tempR3.lt.0.01) tempR3=0.01
      if(tempR4.lt.0.01) tempR4=0.01
      if(tempR5.lt.0.01) tempR5=0.01
      errNorm(1,4)=tempR1
      errNorm(1,5)=tempR2
      if(abs(err(1,4))/errNorm(1,4).lt.0.01.and.
     1   abs(err(1,5))/errNorm(1,5).lt.0.01.and.
     1   abs(err(1,2))/errNorm(1,2).lt.0.01.and.
     1   abs(err(1,3))/errNorm(1,3).lt.0.01.and.
     1   abs(err(1,1))/errNorm(1,1).lt.0.01.and.
     1   abs(err(1,6))/errNorm(1,6).lt.0.01.and.
     1   abs(err(1,7))/errNorm(1,7).lt.0.01.and.
     1   iClMkt.ne.iClMktBreak) iClMktBreak=iClMkt+1!goto 1350

      tempF6=0
      tempF7=0
      tempF8=0
      tempF9=0
      tempF10=0
      tempF13=0
      tempF14=0
      do i=1,25
       tempF1=abs(Wage-WageLast(i))
       tempF2=abs(Rent1-Rent1Last(i))
       tempF3=abs(Rent2-Rent2Last(i))
       tempF4=abs(RP1-RP1last(i))
       tempF5=abs(RP2-RP2last(i))
       tempF11=abs(RCprob(1)-RCprobLast(i,1))
       tempF12=abs(RCprob(2)-RCprobLast(i,2))
       if(tempF1.gt.tempF6) tempF6=tempF1
       if(tempF2.gt.tempF7) tempF7=tempF2
       if(tempF3.gt.tempF8) tempF8=tempF3
       if(tempF4.gt.tempF9) tempF9=tempF4
       if(tempF5.gt.tempF10) tempF10=tempF5
       if(tempF11.gt.tempF13) tempF13=tempF11
       if(tempF12.gt.tempF14) tempF14=tempF12
      end do
      if(tempF6.lt.0.00003.and.tempF7.lt.0.0000002.and.
     1   tempF8.lt.0.0000002.and.tempF9.lt.0.0000002.and.
     1   tempF10.lt.0.0000002.and.tempF13.lt.0.001.and.
     1   tempF14.lt.0.001.and.
     1   iClMkt.ne.iClMktBreak) iClMktBreak=iClMkt+1!goto 1350

      do i=1,24
       WageLast(25+1-i)=WageLast(25-i)
       Rent1Last(25+1-i)=Rent1Last(25-i)
       Rent2Last(25+1-i)=Rent2Last(25-i)
       RP1Last(25+1-i)=RP1Last(25-i)
       RP2Last(25+1-i)=RP2Last(25-i)
       RCprobLast(25+1-i,1)=RCprobLast(25-i,1)
       RCprobLast(25+1-i,2)=RCprobLast(25-i,2)
      end do
      WageLast(1)=Wage
      Rent1Last(1)=Rent1
      Rent2Last(1)=Rent2
      RP1last(1)=RP1
      RP2last(1)=RP2
      RCprobLast(1,1)=RCprob(1)
      RCprobLast(1,2)=RCprob(2)

      if(iClMkt.eq.iClMktBreak-1) then
       Wage=WageBest
       Rent1=Rent1best
       Rent2=Rent2best
       RP1=RP1best
       RP2=RP2best
       RCprob(1)=RCprobBest(1)
       RCprob(2)=RCprobBest(2)
      end if

      if(iClMkt.eq.iClMktBreak) goto 1350

      end do !iClMkt

 1350  continue

      outputErr(t,1)=err(1,1)/errNorm(1,1)
      outputErr(t,2)=err(1,2)/errNorm(1,2)
      outputErr(t,3)=err(1,3)/errNorm(1,3)
      outputErr(t,4)=err(1,4)/errNorm(1,4)
      outputErr(t,5)=err(1,5)/errNorm(1,5)
      outputErr(t,6)=err(1,6)/errNorm(1,6)
      outputErr(t,7)=err(1,7)/errNorm(1,7)

      end
!---------------------------------------------
!Increasing sort
!SortIndx(i)=j --> The j-th entry of the original data is i-th lowest, is in i-th entry of new data
      SUBROUTINE SORT(Dist,N,SortIndx)
      implicit none

      integer N,i,tempI1,SortIndx(N)
      real Dist(N),temp

      do i=1,N
       SortIndx(i)=i
      end do
      i=1
      do while(i.lt.N)
1021   continue
       if(Dist(i).le.Dist(i+1)) then
        goto 1022
       else
        temp=Dist(i+1)
        tempI1=SortIndx(i+1)
        Dist(i+1)=Dist(i)
        SortIndx(i+1)=SortIndx(i)
        Dist(i)=temp
        SortIndx(i)=tempI1
        if(i.gt.1) then
         i=i-1
        end if
        goto 1021
       end if
1022   continue
       i=i+1
      end do

      end
!-------------------------------------------
      subroutine InitAgeInd(nAgent,nAge,nRet,
     1                      NumDeadR,NumDeadW,NumRetired,NumBorn)
      USE IFPORT
      implicit none
      integer nAgent,TotYears,i,t,nAge,nRet
      parameter(TotYears=25000)
      integer AgeInd(nAgent),AgeIndNext(nAgent)
      real NumDeadR,NumDeadW,NumRetired,Numborn,ProbDeath(nAge)
      real tempR1,tempR2,tempR3,AgeIndReal(nAgent)
      real fractionAlive(nAge),fractionDead(nAge),totalAlive
      real fractionDeadW,fractionDeadR,fractionRetired
      real BeqProb(nAge)

      call readdata(ProbDeath,'prbdth.txt',nAge,1,nAge,1)

      do i=1,nAgent
       AgeIndNext(i)=mod(i-1,nAge)+1
      end do
      NumDeadR=0
      NumDeadW=0
      NumRetired=0
      do t=1,TotYears
!If parallelize then NumRetired jumps around due to randomness - so don't parallelize
!c$omp parallel
!c$omp& default(none)
!c$omp& shared(i,nAgent,AgeInd,AgeIndNext,tempR1,ProbDeath)
!c$omp do
       do i=1,nAgent
        AgeInd(i)=AgeIndNext(i)
        tempR1=rand()
        if(tempR1.le.ProbDeath(AgeInd(i))) then
         AgeIndNext(i)=1
        else
         AgeIndNext(i)=AgeInd(i)+1
        end if
       end do
!c$omp end do
!c$omp end parallel
       if(t.gt.100) then
        tempR1=0
        tempR2=0
        tempR3=0
        do i=1,nAgent
         if(AgeIndNext(i).eq.1) then
          if(AgeInd(i).gt.nAge-nRet) then
           tempR1=tempR1+1
          else
           tempR2=tempR2+1
          end if
         end if
         if(AgeInd(i).gt.nAge-nRet) tempR3=tempR3+1
         if(t.eq.TotYears) AgeIndReal(i)=real(AgeInd(i))
        end do
        NumDeadR=NumDeadR+tempR1
        NumDeadW=NumDeadW+tempR2
        NumRetired=NumRetired+tempR3
       end if
      end do
      NumDeadW=NumDeadW/real(TotYears-100)
      NumDeadR=NumDeadR/real(TotYears-100)
      NumRetired=NumRetired/real(TotYears-100)

      write(6,*) NumRetired,NumDeadW,NumDeadR,NumDeadW+NumDeadR

      call writedata(AgeIndReal,'AgeInt.txt',nAgent,1,nAgent,1)

!Suppose 1 agent is born each period.
!ProbDeath(i)=probability of dying just after age i
!fractionAlive(i)=product_{j=1,i-1}[1-ProbDeath(j)] = fraction alive at the start of period i (define product_{j=1,0}[1-ProbDeath(i)]=1)
!fractionDead(i)=ProbDeath(i)*fractionAlive(i)=ProbDeath(i)*product_{j=1,i-1}[1-ProbDeath(j)] = fraction that die just after period i
!totalAlive=sum_{[fractionAlive(i)]
!The above is all in fractions so that TotalAlive/1.0 = nAgent/NumBorn
! This implies that it should be the case that: 1 = sum_{i=1,nAge} [ProbDeath(i) * [product_{j=1,i-1} (1-ProbDeath(j))]]
!If the average bequest size is Beq then total bequests left should be NumberDead*Beq
!The total bequests received by an agent of age i should be NumberBorn*Beq*BeqProb(i)*fracAlive(i)=NumberBorn*Beq*BeqProb(i)*product_{j=1,i-1}[1-ProbDeath(j)]
!The total bequests of all agents should be NumberBorn*Beq*sum_{i=1,nAge}[BeqProb(i)*product_{j=1,i-1}[1-ProbDeath(j)]]
!Thus BeqProb satisfies: 1=sum_{i=1,nAge}[BeqProb(i)*product_{j=1,i-1}[1-ProbDeath(j)]]
!If agents of age=1,n have uniform bequest probability then:
!  BeqProb(k)=1 / sum_{i=1,n}[product_{j=1,i-1}[1-ProbDeath(j)]] for k=1,n
!  BeqProb(i)=1 / sum_{i=1,n} fractionAlive(i)
      fractionAlive(1)=1.0          !this is the fraction alive entering period i, if there was 1 agent born
      fractionDead(1)=ProbDeath(1)  !this number who die just after period i, if there was 1 agent born
      fractionDeadW=fractionDead(1) !This is the total number that die by the end of age=nAge-nRet, if there was 1 agent born
      fractionDeadR=0               !This is the total number that die after age=nAge-nRet, if there was 1 agent born
      totalAlive=1.0
      fractionRetired=0.0
      do i=2,nAge
       fractionAlive(i)=fractionAlive(i-1)*(1.0-ProbDeath(i-1))
       totalAlive=totalAlive+fractionAlive(i)
       if(i.lt.nAge) then
        fractionDead(i)=fractionAlive(i)*ProbDeath(i)
       else
        fractionDead(i)=fractionAlive(i)
       end if
       if(i.le.nAge-nRet) then
        fractionDeadW=fractionDeadW+fractionDead(i)
       else
        fractionDeadR=fractionDeadR+fractionDead(i)
        fractionRetired=fractionRetired+fractionAlive(i)
       end if
      end do

      NumBorn=real(nAgent)/totalAlive
      NumDeadW=NumBorn*fractionDeadW
      NumDeadR=NumBorn*fractionDeadR
      NumRetired=NumBorn*fractionRetired

      write(6,*) NumBorn,fractionRetired,NumRetired

!Check that:
! 1) fractionAlive+fractionDead=1
! 2) NumDeadW, NumDeadR, and NumRetired are consistent w/ previous calculation
! 3) 1 = sum_{i=1,nAge} [ProbDeath(i) * { product_{j=1,i-1} (1-ProbDeath(j)) } ]

!checks 1 and 2
      write(6,*) NumRetired,NumDeadW,NumDeadR,NumDeadW+NumDeadR,NumBorn
!check 3
      tempR1=1.0
      tempR2=ProbDeath(1)
      do i=2,nAge
       tempR1=tempR1*(1.0-ProbDeath(i-1))
       if(i.lt.nAge) then
        tempR2=tempR2+ProbDeath(i)*tempR1
       else
        tempR2=tempR2+tempR1
       end if
      end do
      write(6,*) tempR1,tempR2

      tempR1=0
      do i=1,10
       tempR1=tempR1+fractionAlive(i)
      end do
      do i=1,nAge
       if(i.le.10) then
        BeqProb(i)=1.0/tempR1
       else
        BeqProb(i)=0.0
       end if
!Use BeqProb below if want only newborns receiving bequests
!       if(i.eq.1) then
!        BeqProb(i)=1.0
!       else
!        BeqProb(i)=0.0
!       end if
       !write(6,*) BeqProb(i)
      end do

      call writedata(BeqProb,'BeqPrb.txt',nAge,1,nAge,1)

      end


!-------------------------------------------------------------------
      subroutine makenwgrid(nAge,nDZ,nNW,NWmin,NWmax)
      implicit none
      integer nAge,nDZ,nNW,i,j
      real tempR1,tempR2,tempR3,tempR4,tempR5
      integer tempI1,tempI2,tempI3,tempI4,tempI5
      real NWmin,NWmax
      real NWbound(nAge*nDZ,2),NWgridAll(nAge*nDZ,nNW)

!This creates a fine NWgrid, conditional on (iAge,iZind) based on min and max NW for that group from simulation
      call readdata(NWbound,'NWbnd0.txt',nDZ*nAge,2,nDZ*nAge,2)
      do i=1,nDZ*nAge

!-------------------------------------------
!This creates a fine grid on (NWmin,NWbound(i,2)*1.5) s.t. intervals b/w gridpoints increase by x%, and first gridpoint d=0.01. x is chosen s.t. upper bound of grid is NWbound(i,2)*1.5
!NWgrid(1)=NWmin
!NWgrid(2)=NWmin+d
!NWgrid(3)=NWmin+d*((1+x)^1)
!NWgrid(i)=NWmin+d*((1+x)^(i-2))=NWmin+d*(1 + (1+x) + (1+x)^2 + ...+ (1+x)^(i-2)) = NWmin+d*(((1+x)^(i-1))-1)/x
!I want to set NWgrid(nNW)=NWmax and NWgrid(nNW-1)=tempR1 --> tempR1-NWmin=d*(((1+x)^(i-1))-1)/x
!Will set tempR1=1.5*NWbound(i,2) but must be bigger than 0.5 and smaller than 0.9*NWmax
       tempR1=NWbound(i,2)*1.5
       if(tempR1.lt.0.5) tempR1=0.5
       if(tempR1.ge.0.9*NWmax) tempR1=0.9*NWmax
       tempR4=10000.0
       do j=1,200
        tempR2=0.25*real(j)/200.0
        tempR3=abs(tempR1-NWmin-
     1       0.01*(((1.0+tempR2)**real(nNW-2))-1.0)/tempR2)
        if(tempR3.lt.tempR4) then
         tempR5=tempR2
         tempR4=tempR3
        end if
       end do
       NWgridAll(i,1)=NWmin
       do j=2,nNW-1
        NWgridAll(i,j)=NWgridAll(i,j-1)+0.01*((1.0+tempR5)**real(j-2))
       end do
       NWgridAll(i,nNW)=NWmax
!-------------------------------------------
!This creates a fine grid on (NWmin,NWbound(i,2)*1.5) s.t. intervals b/w gridpoints increase by 10%, and first gridpoint d is chosen s.t. upper bound of grid is NWbound(i,2)*1.5
!NWgrid(1)=NWmin
!NWgrid(2)=NWmin+d
!NWgrid(3)=NWmin+d*(1.1^1)
!NWgrid(i)=NWmin+d*(1.1^(i-2))=NWmin+d*(1 + 1.1 + 1.1^2 + ...+ 1.1^(i-2)) = NWmin+d*((1.1^(i-1))-1)/0.1
!I want to set NWgrid(nNW)=NWmax and NWgrid(nNW-1)=tempR1 --> d=(tempR1-NWmin)*0.1/((1.1^(nNW-2))-1)
!Will set tempR1=1.5*NWbound(i,2) but must be bigger than 0.5 and smaller than 0.9*NWmax
!       tempR1=NWbound(i,2)*1.5
!       if(tempR1.lt.0.5) tempR1=0.5
!       if(tempR1.ge.0.9*NWmax) tempR1=0.9*NWmax
!       tempR2=(tempR1-NWmin)*0.1/((1.1**real(nNW-2))-1.0)
!       NWgridAll(i,1)=NWmin
!       do j=2,nNW-1
!        NWgridAll(i,j)=NWgridAll(i,j-1)+tempR2*(1.1**real(j-2))
!       end do
!       NWgridAll(i,nNW)=NWmax

!-------------------------------------------
!This creates a fine grid on (NWbound(i,1),NWbound(i,2))
!       tempR1=NWbound(i,1)-0.05
!       if(tempR1.lt.NWmin) tempR1=NWmin
!       tempR2=NWbound(i,2)+0.05
!       if(tempR2.gt.NWmax) tempR2=NWmax
!       if(tempR2.lt.0.10) tempR2=0.10
!       tempR3=(((tempR2-tempR1)/(NWmax-NWmin))**0.25) !fraction of gridpoints b/w NWbound(i,1) and NWbound(i,2)
!       tempR4=(1.0-tempR3)*(tempR1-NWmin)/(tempR1-NWmin+NWmax-tempR2)  !fraction of gridpoints below NWbound(i,1)
!       tempR5=(1.0-tempR3)*(NWmax-tempR2)/(tempR1-NWmin+NWmax-tempR2)  !fraction of gridpoints above NWbound(i,1)
!       tempI1=nint(real(nNW)*tempR4)     !number of points in (NWmin,NWbound(i,1))
!       tempI3=nint(real(nNW)*tempR5)     !number of points in (NWbound(i,2),NWmax)
!       if(tempI1.lt.1) tempI1=1
!       if(tempI2.lt.1) tempI2=1
!       tempI2=nNW-tempI1-tempI3          !umber of points in (NWbound(i,1),NWbound(i,2))
!       if(tempI1.gt.1) then
!        do j=1,tempI1
!         NWgridAll(i,j)=NWmin+(tempR1-NWmin)*real(j-1)/real(tempI1-1)
!        end do
!       else
!        NWgridAll(i,1)=NWmin
!       end if
!       if(tempI3.gt.1) then
!        do j=1,tempI3
!         NWgridAll(i,nNW-tempI3+j)=tempR2+
!     1                        (NWmax-tempR2)*real(j-1)/real(tempI3-1)
!        end do
!       else
!        NWgridAll(i,nNW)=NWmax
!       end if
!       do j=1,tempI2
!        NWgridAll(i,tempI1+j)=tempR1+
!     1                       (tempR2-tempR1)*real(j)/real(tempI2+1)
!       end do

!        write(6,'(i4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,
!     1               f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,
!     1               f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,
!     1               f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,
!     1               f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,f8.4,
!     1               f8.4,f8.4,f8.4,f8.4,f8.4)')
!     1 i,(NWgridAll(i,j),j=1,nNW)


      end do

      call writedataNW(NWgridAll,'NWgrid.txt',nAge*nDZ,nNW,nAge*nDZ,nNW)

      end
!-------------------------------------------------------------------
!This computes various moments of the bequest distribution
      SUBROUTINE BeqDistMoments(nAgent,nDZ,nDepr,nBeqDist,NumDead,
     1           BeqInd,PH,taxprop,deprH,deprINV0,DeprGrid,fracBeq,
     1           BeqNtile1,BeqNtile2,RCavgrent,nLOC,nHF,iHF,t)
      implicit none
      integer nAgent,nDZ,nBeqDist,countBeq1,countBeq2,i,j,t,nDZtemp
      integer tempI1,tempI2,tempI3,nDepr
      real tempR1,DeprGrid(nDepr)
      real BeqInd(nAgent,7),PH(2),taxprop(nHF,nLOC)
      real AvgBeq0,AvgBeq1,AvgBeq2,NumDead,deprH(nLOC),deprINV0,fracBeq
      real BeqInd0(nAgent),BeqInd1(nAgent),BeqInd2(nAgent)
      integer SortIndex(nAgent),nLOC,nHF,iHF
      real BeqNtile1(nBeqDist),BeqNtile2(nBeqDist),RCavgrent(nLOC,nHF)

      nDZtemp=nDZ/2
      if(fracBeq.lt.0.00001) nDZtemp=nDZ

      do i=1,nAgent
       BeqInd0(i)=0
       BeqInd1(i)=0
       BeqInd2(i)=0
      end do

      countBeq1=0
      countBeq2=0
      do i=1,nint(NumDead)
       BeqInd0(i)=BeqInd(i,1)+
     1  (1.0-deprH(1)*DeprGrid(nint(BeqInd(i,7)))-taxprop(iHF,1))*
     1   BeqInd(i,2)*PH(1)+
     1  (1.0-deprH(2)*DeprGrid(nint(BeqInd(i,7)))-taxprop(iHF,2))*
     1   BeqInd(i,3)*PH(2)+
     1  (1.0-deprH(1)*DeprGrid(nint(BeqInd(i,7)))-
     1   taxprop(iHF,1)-deprINV0)*BeqInd(i,4)*PH(1)*RCavgrent(1,iHF)+
     1  (1.0-deprH(2)*DeprGrid(nint(BeqInd(i,7)))-
     1   taxprop(iHF,2)-deprINV0)*BeqInd(i,5)*PH(2)*RCavgrent(2,iHF)
       if(nint(BeqInd(i,6)).le.nDZtemp) then
        BeqInd1(i)=BeqInd0(i)
        BeqInd2(i)=0
        countBeq1=countBeq1+1
       else
        BeqInd1(i)=0
        BeqInd2(i)=BeqInd0(i)
        countBeq2=countBeq2+1
       end if
      end do
      call sort(BeqInd0,nAgent,SortIndex)
      call sort(BeqInd1,nAgent,SortIndex)
      call sort(BeqInd2,nAgent,SortIndex)
      AvgBeq0=0
      do i=nAgent-nint(NumDead)+1,nAgent
       AvgBeq0=AvgBeq0+BeqInd0(i)/NumDead
      end do
      AvgBeq1=0
      do i=nAgent-countBeq1+1,nAgent
       AvgBeq1=AvgBeq1+BeqInd1(i)/real(countBeq1)
      end do
      AvgBeq2=0
      do i=nAgent-countBeq2+1,nAgent
       AvgBeq2=AvgBeq2+BeqInd2(i)/real(countBeq2)
      end do


!      if(mod(t,7).eq.0)
!     1 write(6,'(f5.0,i5,i5,f9.3,f9.3,f9.3)')
!     1 NumDead,countBeq1,countBeq2,AvgBeq0,AvgBeq1,AvgBeq2


      do j=1,nBeqDist

       if(countBeq1.gt.0) then
        tempI1=nAgent-countBeq1+1+
     1         nint(real(j-1)*real(countBeq1)/real(nBeqDist))
        tempI2=nAgent-countBeq1+
     1         nint(real(j+1-1)*real(countBeq1)/real(nBeqDist))
        if(tempI1.lt.nAgent-countBeq1+1) tempI1=nAgent-countBeq1+1
        if(tempI2.gt.nAgent) tempI2=nAgent
        if(tempI2.lt.tempI1) tempI2=tempI1
        tempR1=0
        do i=tempI1,tempI2
         tempR1=tempR1+BeqInd1(i)/real(1+tempI2-tempI1)
        end do
        BeqNtile1(j)=tempR1
       else
        BeqNtile1(j)=AvgBeq0
       end if

       if(countBeq2.gt.0) then
        tempI1=nAgent-countBeq2+1+
     1         nint(real(j-1)*real(countBeq2)/real(nBeqDist))
        tempI2=nAgent-countBeq2+
     1         nint(real(j+1-1)*real(countBeq2)/real(nBeqDist))
        if(tempI1.lt.nAgent-countBeq2+1) tempI1=nAgent-countBeq2+1
        if(tempI2.gt.nAgent) tempI2=nAgent
        if(tempI2.lt.tempI1) tempI2=tempI1
        tempR1=0
        do i=tempI1,tempI2
         tempR1=tempR1+BeqInd2(i)/real(1+tempI2-tempI1)
        end do
        BeqNtile2(j)=tempR1
       else
        BeqNtile2(j)=AvgBeq0
       end if

      end do

      end

!!-------------------------------------------------------------------
!!This creates look-up grid to get C from N using:
!!c=((1-aN)*(1-aH)*g(R)*X*W*G*z/(aN*chi*((1-CommCost-Hours)^(chi*elastCN-1))))^(1/(1-elastCN))
!      SUBROUTINE LookupConsHours(nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF,nNW,nDZ)
!      implicit none
!      integer nWage,nRent1,nRent2,nRP1,nRP2,nH1,nH2,nHF,nNW,nDZ
!      integer iWage,iRent1,iRent2,iRP1,iRP2,iH1,iH2,iHF,iNW,iDZ
!      integer nAgg,nInd,iAgg,iInd
!      integer tempI1
!      nAgg=nWage*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF
!      nInd=nNW*nDZ

!      do iAgg=1,nAgg
!!       iAgg=(iWage-1)*nRent1*nRent2*nRP1*nRP2*nH1*nH2*nHF+
!!     1      (iRent1-1)*nRent2*nRP1*nRP2*nH1*nH2*nHF+
!!     1      (iRent2-1)*nRP1*nRP2*nH1*nH2*nHF+
!!     1      (iRP1-1)*nRP2*nH1*nH2*nHF+
!!     1      (iRP2-1)*nH1*nH2*nHF+(iH1-1)*nH2*nHF+(iH2-1)*nHF+iHF
!       iHF=mod(iAgg-1,nHF)+1
!       tempI1=1+(iAgg-iHF)/nHF
!       iH2=mod(tempI1-1,nH2)+1
!       tempI1=1+(tempI1-iH2)/nH2
!       iH1=mod(tempI1-1,nH1)+1
!       tempI1=1+(tempI1-iH1)/nH1
!       iRP2=mod(tempI1-1,nRP2)+1
!       tempI1=1+(tempI1-iRP2)/nRP2
!       iRP1=mod(tempI1-1,nRP1)+1
!       tempI1=1+(tempI1-iRP1)/nRP1
!       iRent2=mod(tempI1-1,nRent2)+1
!       tempI1=1+(tempI1-iRent2)/nRent2
!       iRent1=mod(tempI1-1,nRent1)+1
!       iWage=1+(tempI1-iRent1)/nRent1
!      end do
!      end

