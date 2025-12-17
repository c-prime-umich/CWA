%% Gaussian Recreation Test

% Author: Timothy J. Welch

clc; clear; close all;

%% Load Parameters
excel_dat = readmatrix("H2AirDetProp.xlsx");
Dm = 5.76;          %RDC mean diameter [in]
phi = 1.46;         %run equivalence ratio

% Interpolate Ucj from provided dat (CodeGen-safe: dat must be regular numeric)
Ucj = interp1(excel_dat(:,1),excel_dat(:,9),phi); % [m/s]

% Convert diameter to meters for frequency normalization
Cd = Dm * pi * 0.0254;   % circumference [m]

% Convert Ucj to randians/s
Dcj = Ucj/Cd*2*pi;           % [rad/s]

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

%% Load plot4 Data
load("plotData.mat")

% Load variables
intens = plot4.intens;
detins = plot4.detins;
cdetins = plot4.cdetins;
crwpins = plot4.crwpins;
maxI = plot4.maxI;
minI = plot4.minI;
ttp = plot4.ttp;
vdets = plot4.vdets;
vcdets = plot4.vcdets;
vcrwps = plot4.vcrwps;

% condition data for NaNs
vdets = fillNaNsLinear(vdets);
vcrwps = fillNaNsLinear(vcrwps);
vcdets = fillNaNsLinear(vcdets);
detins = fillNaNsLinear(detins);
crwpins = fillNaNsLinear(crwpins);
cdetins = fillNaNsLinear(cdetins);

%% Create Synthetic Data
t_syn = linspace(t(1),t(end),length(t));
dth_syn = 2*pi/length(thetap);
thetap_syn = 0:dth_syn:2*pi-dth_syn;
XT_syn = zeros(length(thetap_syn),length(t_syn));

%% Advect Gaussian
% Parameters for advection
dt = t(2)-t(1);
L = 2*pi;

% wave 1
A1 = 1;
sigma1 = 0.3;
[~, xc_idx] = max(XT(:,1));
xc1 = thetap_syn(xc_idx);

% wave 2
A2 = 1;
sigma2 = 0.2;
xc2 = thetap_syn(xc_idx);

% wave 3
A3 = 1;
sigma3 = 0.1;
xc3 = thetap_syn(xc_idx);

% advect Gaussians
for it = 1:length(t)
    [gs1,xc1] = advectGaussian_step(thetap_syn,t_syn(it),vdets,ttp,Dcj,detins,L,A1,sigma1,xc1,dt);
    [gs2,xc2] = advectGaussian_step(thetap_syn,t_syn(it),vcrwps,ttp,Dcj,crwpins,L,A2,sigma2,xc2,dt);
    [gs3,xc3] = advectGaussian_step(thetap_syn,t_syn(it),vcdets,ttp,Dcj,cdetins,L,A3,sigma3,xc3,dt);

    % Update XT_syn
    % XT_syn(:,it) = gs1;
    XT_syn(:,it) = gs1+gs2+gs3;
end


%% Plot
% Original XT Diagram
figure()
set(gcf, 'Position', [200 200 2500 600])
subplot('Position', [.1 .3 .8 .6])
imagesc(t, thetap, XT)
set(gca, 'Ydir', 'Normal')
title(['Run ', num]);
xlabel('Time [s]');
ylabel('$\theta$');
axis([ t(1) t(1)+300/fps 0 max(thetap)])
% formatPlot(gca,20)
subplot('Position', [.1 .12 .8 .03])
hold on
imagesc(t,thetap, XT)
plot([t(1) t(1)], [0 2*pi], 'r-', 'LineWidth', 3)
plot([t(301) t(301)], [0 2*pi], 'r-', 'LineWidth', 3)
hold off
axis([t0(1) t(end) 0 max(thetap)])
% formatPlot(gca,20)
set(gcf,'PaperPositionMode','auto')
set(gca, 'YColor', 'none')
set(gcf,'color','w');

% Synthesized XT Diagram
figure()
set(gcf, 'Position', [200 200 2500 600])
subplot('Position', [.1 .3 .8 .6])
imagesc(t_syn, thetap_syn, XT_syn)
set(gca, 'Ydir', 'Normal')
title(['Run ', num]);
xlabel('Time [s]');
ylabel('$\theta$');
axis([ t_syn(1) t_syn(1)+300/fps 0 max(thetap_syn)])
% formatPlot(gca,20)
subplot('Position', [.1 .12 .8 .03])
hold on
imagesc(t_syn,thetap_syn,XT_syn)
plot([t_syn(1) t_syn(1)], [0 2*pi], 'r-', 'LineWidth', 3)
plot([t_syn(301) t_syn(301)], [0 2*pi], 'r-', 'LineWidth', 3)
hold off
axis([t0(1) t_syn(end) 0 max(thetap_syn)])
% formatPlot(gca,20)
set(gcf,'PaperPositionMode','auto')
set(gca, 'YColor', 'none')
set(gcf,'color','w');

%% Functions
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
    dx = x - x0;
    dx = mod(dx + L/2, L) - L/2;
    
    g = A * exp( - dx.^2 / (2*sigma^2) );
end

function [gx,xc] = advectGaussian_step(theta,t,vFunc,tFunc,Dcj,intensFunc,L,A,sigma,xc,dt)
    % get velocity
    v = interp1(tFunc,vFunc,t,'linear','extrap');
    v = v*Dcj;    % convert to [rad/s]

    % get new intensity
    A = A*interp1(tFunc,intensFunc,t,'linear','extrap');

    % update center using velocity
    xc = xc + v*dt;

    % wrap to periodic domain
    xc = mod(xc,L);

    % compute Gaussian shape at this time
    gx = periodicGaussian(theta,xc,A,sigma);
end

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