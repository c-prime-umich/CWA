%% Fully Resolved Gaussian Parameter Optimization Wrapper

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
XT_clean = 0*XT;

for i=0:(Nfr-1)/win-1
    XT_clean(:,(win*i+1:win*(i+1))) = XT(:,(win*i+1:win*(i+1))) - min(XT(:,(win*i+1:win*(i+1))),[],2)*ones(1,win);
end
XT_clean(XT_clean<0) = 0;

%% Load plot4 Data
load("plot4_data_conditioned.mat")
vdets = fillNaNsLinear(plot4.vdets)*Dcj;
vcdets = fillNaNsLinear(plot4.vcdets)*Dcj;
vcrwps = fillNaNsLinear(plot4.vcrwps)*Dcj;

%% 1st Optimization (vdets)
fname = "data/wave1_opt_results.mat";
[theta0,sigma,A,v] = Gauss_Wave_Opt(XT_clean,Nfr,Nb,thetap,t,vdets,fname);

% prep for second optimization
XT_prepped = XT_Prepper(XT_clean,Nfr,Nb,theta0,sigma,A);

%% 2nd Optimization (vcrwps)
fname = "data/wave2_opt_results.mat";
[theta0,sigma,A,v] = Gauss_Wave_Opt(XT_prepped,Nfr,Nb,thetap,t,vcrwps,fname);

% prep for second optimization
XT_prepped = XT_Prepper(XT_prepped,Nfr,Nb,theta0,sigma,A);

%% 3rd Optimization (vcdets)
fname = "data/wave3_opt_results.mat";
[theta0,sigma,A,v] = Gauss_Wave_Opt(XT_prepped,Nfr,Nb,thetap,t,vcdets,fname);


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

function XT_cleared = XT_Prepper(XT,Nfr,Nb,theta0,sigma,A)
    % Create Synthetic Data
    dth_syn = 2*pi/Nb;
    thetap_syn = 0:dth_syn:2*pi-dth_syn;
    XT_syn = zeros(Nb,Nfr);
    
    
    % create Gaussian
    for i = 1:Nfr
        gs = periodicGaussian(thetap_syn,theta0(i),A(i),sigma(i));
    
        % Update XT_syn
        XT_syn(:,i) = gs;
    end
    
    % Clear Wave
    mult_fac = 2;
    XT_cleared = XT-mult_fac*XT_syn;
    XT_cleared(XT_cleared<0) = 0;
end

function g = periodicGaussian(x,x0,A,sigma)
    % periodicGaussian
    % Returns a Gaussian on a periodic domain [0,2pi)
    %
    % x     : vector of gridpoints
    % x0    : center location
    % A     : amplitude (peak height)
    % sigma : RMS width
    
    L = 2*pi;
    
    % shortest signed distance on periodic domain
    dx = mod((x - x0) + L/2, L) - L/2;
    
    g = A * exp( - dx.^2 / (2*sigma^2) );
end