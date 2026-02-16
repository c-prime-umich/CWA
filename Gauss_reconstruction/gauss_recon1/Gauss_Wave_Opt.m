function Gauss_Wave_Opt(XT,Nfr,Nb,vdets)
%% Fully Resolved Single Wave Optimization Function

% Author: Timothy J. Welch

% INPUTS:
%
%
%
%
%% Initialize Variables
A = zeros(Nfr,1);
theta0 = zeros(Nfr,1);
sigma = zeros(Nfr,1);
v = zeros(Nfr,1); v(1) = vdets(1);
vdets_avg = mean(vdets);

low_j = 1; up_j = Nb;

%% Optimize
for i=1:Nfr
    if low_j < up_j
        XT_i = XT(low_j:up_j,i);
    else
        XT_i = [XT(1:up_j,i);XT(low_j:Nb,i)];
    end
    % XT_i = XT(low_j:up_j,i);
    A(i) = max(XT_i);
    [~,theta_i] = min(abs(XT(:,i)-A(i)));
    theta0(i) = thetap(theta_i);

    % Define parameter bounds
    lb = 0.1; ub = 0.7;

    % Initial guess
    p0 = 0.3;

    % Other optimization paramters
    other_params = [A(i),theta0(i),Nb,low_j,up_j];

    % Objective function
    objFun1 = @(p) objectiveWrapperSigma(p,XT,other_params,i);

    % Optimization settings
    options = optimoptions('fmincon',...
        'Algorithm','sqp',...
        'Display','none',...
        'MaxFunctionEvaluations', 2e5,...
        'MaxIterations', 500,...
        'OptimalityTolerance',1e-40,...
        'UseParallel', false);

    % Run optimization
    [p_opt,fval,exitflag,output] = fmincon(objFun1,p0,[],[],[],[],lb,ub,[],options);
    if mod(i,1000) == 0
        disp("index: "+num2str(i)+"    sigma: "+num2str(p_opt))
    end

    % save sigma
    sigma(i) = p_opt;

    % calculate v
    if i < Nfr
        v(i+1) = (theta0(i+1)-theta0(i))/dt;
    end

    % calculate new bounds
    if vdets_avg < 0
        theta0_guess_up = mod(theta0(i)+0.7*vdets_avg*dt,2*pi);
        theta0_guess_low = mod(theta0(i)+1.3*vdets_avg*dt,2*pi);
        [~,up_j] = min(abs(thetap-theta0_guess_up));
        [~,low_j] = min(abs(thetap-theta0_guess_low));
    else
        theta0_guess_up = mod(theta0(i)+1.3*vdets_avg*dt,2*pi);
        theta0_guess_low = mod(theta0(i)+0.7*vdets_avg*dt,2*pi);
        [~,up_j] = min(abs(thetap-theta0_guess_up));
        [~,low_j] = min(abs(thetap-theta0_guess_low));
    end
end

%% Save data
save("opt_results_resolved_window.mat","theta0","sigma","A","v")


%% Objective Function Wrapper
function val = objectiveWrapperSigma(p,XT_target,other_params,i)
    % Unpack p
    sigmaf = p;

    % Unpack other parameters
    Af = other_params(1);
    xc = other_params(2);
    Nbf = other_params(3);
    low_jf = other_params(4);
    up_jf = other_params(5);

    % Compute model array based on parameters
    XT_syn = Gaussian_Syn_Func_Resolved(Nbf,Af,sigmaf,xc);


    % % cost = L1 norm
    % if low_jf < up_jf
    %     diff = XT_syn(low_jf:up_jf) - XT_target(low_jf:up_jf,i);
    % else
    %     diff = [XT_syn(1:up_jf);XT_syn(low_jf:Nbf)] - [XT_target(1:up_jf,i);XT_target(low_jf:Nbf,i)];
    % end
    % val = sum(abs(diff),"all");
    
    % cost = Linf norm
    diff = XT_syn - XT_target(:,i);
    val = max(abs(diff),[],"all");
end




end