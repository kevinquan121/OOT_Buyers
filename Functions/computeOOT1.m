function f=computeOOT1(a1, high, HFgrid1, outten, outseven, taxpropOOT) 
    ForDemTot(:,1)=exp(a1.* ones(2000,1)-HFgrid1.*log(outten.*(1+taxpropOOT))); %this is foreign demand per capita in Z1
    f=mean(ForDemTot(high,1)./outseven(high)); %share of OOT demand in Z1
end

