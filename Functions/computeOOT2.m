function f=computeOOT2(a2, high, HFgrid1, outten, outseven, taxpropOOT) 
    ForDemTot(:,1)=exp(a2.* ones(2000,1)-HFgrid1.*log(outten.*(1+taxpropOOT))); %this is foreign demand per capita in Z1
    f=mean(ForDemTot(high,1)./outseven(high)); %share of OOT demand in Z1
end