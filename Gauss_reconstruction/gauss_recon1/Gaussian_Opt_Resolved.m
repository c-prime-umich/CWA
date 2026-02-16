%% Fully Resolved Gaussian Parameter Optimization

% Author: Timothy J. Welch

clc; clear; close all;

%% Load Original XTData
run = 3433;
XTdir = '/Users/tjwelch/Desktop/APCL/Research_Projects/Formal Verification/CWA_Local/XT Diagrams';
num = num2str(run,'%05.0f');
XTfile_full = [XTdir,'/Run_', num, '-full.mat'];
XTStruct_full = load(XTfile_full);
XT = XTStruct_full.XT;
t0 = XTStruct_full.t0;
fps = XTStruct_full.fps;
[Nb,Nfr] = size(XT);

dth = 2*pi/Nb;
thetap = 0:dth:2*pi-dth;

t = (0:Nfr-1)/fps + t0;
dt = t(2)-t(1);

%% Load Run Data
excel_dat = readmatrix("H2AirDetProp.xlsx");
Dm = 5.76;          %RDC mean diameter [in]
phi = 1.46;         %run equivalence ratio

% Interpolate Ucj from provided dat (CodeGen-safe: dat must be regular numeric)
Ucj = interp1(excel_dat(:,1),excel_dat(:,9),phi); % [m/s]

% Convert diameter to meters for frequency normalization
Cd = Dm * pi * 0.0254;   % circumference [m]

% Convert Ucj to randians/s
Dcj = Ucj/Cd*2*pi;           % [rad/s]

%% "Clean" XTData
win=20;

for i=0:(Nfr-1)/win-1
    XT(:,(win*i+1:win*(i+1))) = XT(:,(win*i+1:win*(i+1))) - min(XT(:,(win*i+1:win*(i+1))),[],2)*ones(1,win);
end
XT(XT<0) = 0;

%% Load plot4 Data
load("plot4_data_conditioned.mat")
vdets = fillNaNsLinear(plot4.vdets)*Dcj;

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
    sigma = p;

    % Unpack other parameters
    A = other_params(1);
    xc = other_params(2);
    Nb = other_params(3);
    low_j = other_params(4);
    up_j = other_params(5);

    % Compute model array based on parameters
    XT_syn = Gaussian_Syn_Func_Resolved(Nb,A,sigma,xc);

    % plot(linspace(0,2*pi,Nb),XT_syn,linspace(0,2*pi,Nb),XT_target(:,i))

    % cost = L1 norm
    if low_j < up_j
        diff = XT_syn(low_j:up_j) - XT_target(low_j:up_j,i);
    else
        diff = [XT_syn(1:up_j);XT_syn(low_j:Nb)] - [XT_target(1:up_j,i);XT_target(low_j:Nb,i)];
    end
    val = sum(abs(diff),"all");
    
    % % cost = Linf norm
    % diff = XT_syn - XT_target(:,i);
    % val = max(abs(diff),[],"all");
end


%% Helper Function(s)
function y = fillNaNsLinear(x)
    % fillNaNsLinear - fill NaNs in vector x by linear interpolation
    %
    % x : nx1 vector
    % y : nx1 vector with NaNs replaced
    
    y = x;
    idx = ~isnan(x);
    
    % only interpolate if there are >=2 points
    if sum(idx) >= 2
        y(~idx) = interp1(find(idx), x(idx), find(~idx),"linear","extrap");
    end
end