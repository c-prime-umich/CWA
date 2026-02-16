%% Gaussian Recreation Resolved

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
T = t(end)-t(1);

%% "Clean" XTData
win=20;

for i=0:(Nfr-1)/win-1
    XT(:,(win*i+1:win*(i+1))) = XT(:,(win*i+1:win*(i+1))) - min(XT(:,(win*i+1:win*(i+1))),[],2)*ones(1,win);
end
XT(XT<0) = 0;

%% Load plot4 Data
% load("plotData.mat")
load("plot4_data_conditioned.mat")

% Load variables
detins = plot4.detins;
cdetins = plot4.cdetins;
crwpins = plot4.crwpins;
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
load("opt_results_resolved_window.mat");
xc1 = theta0(1);
dt = t(2)-t(1);

% Smooth?
% sigma = smooth(t,sigma,100*dt,'moving');
% sigma = movmean(movmean(sigma,1000),1000);
% sigma = movmean(sigma,1000);
% A = movmean(A,1000);

% advect Gaussians
for i = 1:length(t)
    % calculate gaussian
    % [gs1,xc1] = advectGaussian_step(thetap_syn,v(i),A(i),sigma(i),xc1,dt);
    gs1 = periodicGaussian(thetap_syn,theta0(i),A(i),sigma(i));

    % Update XT_syn
    XT_syn(:,i) = gs1;
end

%% Call Checker
ep = checker(XT,XT_syn,1);
writematrix(XT, 'XT.txt', 'Delimiter', 'space');
writematrix(XT_syn, 'XT_syn.txt', 'Delimiter', 'space');

%% Clear Wave 1
XT_cleared = XT-100*XT_syn;
XT_cleared(XT_cleared<0) = 0;


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

% Difference XT Diagram
figure()
set(gcf, 'Position', [200 200 2500 600])
subplot('Position', [.1 .3 .8 .6])
imagesc(t_syn, thetap_syn, XT-XT_syn)
set(gca, 'Ydir', 'Normal')
title(['Run ', num]);
xlabel('Time [s]');
ylabel('$\theta$');
axis([ t_syn(1) t_syn(1)+300/fps 0 max(thetap_syn)])
% formatPlot(gca,20)
subplot('Position', [.1 .12 .8 .03])
hold on
imagesc(t_syn,thetap_syn,XT-XT_syn)
plot([t_syn(1) t_syn(1)], [0 2*pi], 'r-', 'LineWidth', 3)
plot([t_syn(301) t_syn(301)], [0 2*pi], 'r-', 'LineWidth', 3)
hold off
axis([t0(1) t_syn(end) 0 max(thetap_syn)])
% formatPlot(gca,20)
set(gcf,'PaperPositionMode','auto')
set(gca, 'YColor', 'none')
set(gcf,'color','w');

% Slice
figure()
set(gcf, 'Position', [200 200 2500 600])

subplot(1,3,1)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Recreation")
xlim([t(1),t(1)+100*T/Nfr])

subplot(1,3,2)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Recreation")
xlim([t(floor(Nfr/2)),t(floor(Nfr/2))+100*T/Nfr])

subplot(1,3,3)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Recreation")
xlim([t(end)-100*T/Nfr,t(end)])

% Slice Subtraction
figure()
set(gcf, 'Position', [200 200 2500 600])

subplot(1,3,1)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT(60,:)-XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Subtraction")
xlim([t(1),t(1)+100*T/Nfr])

subplot(1,3,2)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT(60,:)-XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Subtraction")
xlim([t(floor(Nfr/2)),t(floor(Nfr/2))+100*T/Nfr])

subplot(1,3,3)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT(60,:)-XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Subtraction")
xlim([t(end)-100*T/Nfr,t(end)])

% Cleared Subtraction
figure()
set(gcf, 'Position', [200 200 2500 600])

subplot(1,3,1)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT_cleared(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Cleared")
xlim([t(1),t(1)+100*T/Nfr])

subplot(1,3,2)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT_cleared(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Cleared")
xlim([t(floor(Nfr/2)),t(floor(Nfr/2))+100*T/Nfr])

subplot(1,3,3)
plot(t,XT(60,:),'LineWidth',2)
hold on
plot(t,XT_cleared(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Cleared")
xlim([t(end)-100*T/Nfr,t(end)])

% A-theta plot
figure()
set(gcf, 'Position', [200 200 2500 600])
subplot(2,2,1)
plot(thetap,XT(:,1),thetap,XT_syn(:,1),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")

subplot(2,2,2)
plot(thetap,XT(:,floor(Nfr/4)),thetap,XT_syn(:,floor(Nfr/4)),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")

subplot(2,2,3)
plot(thetap,XT(:,2*floor(Nfr/4)),thetap,XT_syn(:,2*floor(Nfr/4)),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")

subplot(2,2,4)
plot(thetap,XT(:,3*floor(Nfr/4)),thetap,XT_syn(:,3*floor(Nfr/4)),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")


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
    dx = mod((x - x0) + L/2, L) - L/2;
    
    g = A * exp( - dx.^2 / (2*sigma^2) );
end

function [gx,xc] = advectGaussian_step(theta,v,A,sigma,xc,dt)
    % update center using velocity
    xc = xc + v*dt;

    % wrap to periodic domain
    L = 2*pi;
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