%% Chained Gaussian Parameter Optimization

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

% Initial guesses
v0 = plot4.vdets(1)*Dcj; % [rad/s]
A0 = plot4.detins(1);

%% Optimization Parameters
N_opt_win = 1000; % number of optimization windows
T_opt_win = (t(end)-t(1))/N_opt_win; % time in each window
didx_opt_win = (Nfr-1)/N_opt_win; % index width of each window

% Initialize coarse function
v = zeros(N_opt_win,1);
A = zeros(N_opt_win,1);
theta0 = zeros(N_opt_win,1);
sigma = zeros(N_opt_win,1);
v(1) = v0;

%% Initial Optimization
% Parameters: C, sigma, theta_0
% Define parameter bounds
lb = [1e1 0.1 0];
ub = [1e5 0.75 2*pi];

% Initial guess
p0 = [1e6 0.3 5.4122];

% Other optimization paramters
other_params = [fps,Nb,v0,A0,didx_opt_win];

% Objective function
objFun1 = @(p) objectiveWrapper1(p,XT,other_params);

% Optimization settings
options = optimoptions('fmincon',...
    'Display','iter',...
    'MaxFunctionEvaluations', 2e5,...
    'MaxIterations', 500,...
    'UseParallel', false);

% Run optimization
[p_opt,fval,exitflag,output] = fmincon(objFun1,p0,[],[],[],[],lb,ub,[],options);

disp("Optimal parameters:")
disp(p_opt)

%% Subsequent Optimizations
% Parameters: A, sigma, v

% Unpack results of 1st opt
A(1) = p_opt(1)*A0; sigma(1) = p_opt(2); theta0(1) = p_opt(3);

% Loop optimizations
for i=1:N_opt_win-1
    % Define parameter bounds
    lb = [1e2 0.9*sigma(1) 1.1*v(i)];
    ub = [1e5 1.1*sigma(1) 0.9*v(i)];
    
    % Initial guess
    v0 = interp1(plot4.ttp,plot4.vdets,mean([t(i*didx_opt_win),t((i+1)*didx_opt_win)]),'linear','extrap')*Dcj;
    % A0 = interp1(plot4.ttp,plot4.detins,mean([t(i*didx_opt_win),t((i+1)*didx_opt_win)]),'linear','extrap');
    p0 = [A(i) sigma(i) v0];
    
    % Other optimization paramters
    other_params = [fps,Nb,theta0(1),didx_opt_win];
    
    % Objective function
    objFun2 = @(p) objectiveWrapperSubsequent(p,XT,other_params,i);
    
    % Optimization settings
    options = optimoptions('fmincon',...
        'Display','iter',...
        'MaxFunctionEvaluations', 2e5,...
        'MaxIterations', 500,...
        'UseParallel', false,...
        'Algorithm','sqp');
    
    % Run optimization
    [p_opt,fval,exitflag,output] = fmincon(objFun2,p0,[],[],[],[],lb,ub,[],options);
    
    disp("Optimal parameters:")
    disp(p_opt)
    
    % Unpack resilts
    A(i+1) = p_opt(1); sigma(i+1) = p_opt(2); v(i+1) = p_opt(3);
    theta0(i+1) = mod(theta0(i) + T_opt_win*v(i+1),2*pi);
end

%% Save data
save("opt_results.mat","theta0","sigma","A","v","didx_opt_win","N_opt_win")


%% Objective Function Wrappers
function val = objectiveWrapper1(p,XT_target,other_params)
    % Unpack p
    C = p(1); sigma = p(2); xc = p(3);

    % Unpack other parameters
    fps = other_params(1);
    Nb = other_params(2);
    v = other_params(3);
    A = other_params(4);
    Nt = other_params(5);

    % Compute model array based on parameters
    XT_syn = Gaussian_Syn_Func(fps,Nb,v,C*A,sigma,xc,Nt);

    % % cost = L1 norm
    % diff = XT_syn - XT_target(:,1:Nt+1);
    % val = sum(abs(diff),"all");

    % cost = Linf norm
    diff = XT_syn - XT_target(:,1:Nt+1);
    val = max(abs(diff),[],"all");
end

function val = objectiveWrapperSubsequent(p,XT_target,other_params,i)
    % Unpack p
    A = p(1); sigma = p(2); v = p(3);

    % Unpack other parameters
    fps = other_params(1);
    Nb = other_params(2);
    xc = other_params(3);
    Nt = other_params(4);

    % Compute model array based on parameters
    XT_syn = Gaussian_Syn_Func(fps,Nb,v,A,sigma,xc,Nt);

    % % cost = L1 norm
    % diff = XT_syn - XT_target(:,Nt*i+1:Nt*(i+1)+1);
    % val = sum(abs(diff),"all");

    % cost = Linf norm
    diff = XT_syn - XT_target(:,Nt*i+1:Nt*(i+1)+1);
    val = max(abs(diff),[],"all");
end