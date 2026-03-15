%% Gaussian Synthesis Runner

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
T = t(end)-t(1);
writematrix(XT,"data/XT.csv");
writematrix(dt,"data/dt.csv");

%% "Clean" XTData
win=20;
XT_cleaned = XT;

for i=0:(Nfr-1)/win-1
    XT_cleaned(:,(win*i+1:win*(i+1))) = XT(:,(win*i+1:win*(i+1))) - min(XT(:,(win*i+1:win*(i+1))),[],2)*ones(1,win);
end
XT_cleaned(XT_cleaned<0) = 0;
XT_subtraction = XT - XT_cleaned;
XT_subtraction4save = XT_subtraction(:,1:win:end);
writematrix(XT_subtraction4save,"data/BG.csv");

%% Create Synthetic Data
t_syn = linspace(t(1),t(end),length(t));
dth_syn = 2*pi/Nb;
thetap_syn = 0:dth_syn:2*pi-dth_syn;
XT_syn = zeros(Nb,Nfr);

%% Add Waves
fnames = ["data/wave1_opt_results.mat","data/wave2_opt_results.mat","data/wave3_opt_results.mat"];
for i=1:length(fnames)
    % load wave
    load(fnames(i));

    % smooth
    sigma = movmean(movmean(sigma,1000),1000);
    A = movmean(movmean(A,1000),1000);
    v = movmean(movmean(v,1000),1000);

    % reduce
    sigma = sigma(1:win:end);
    A = A(1:win:end);
    v = v(1:win:end);

    % for k=2:Nfr
    %     theta0(k) = theta0(k-1) + v(k-1)*dt; % needed to match C
    % end

    % add wave
    XT_syn = add_wave(XT_syn,Nfr,thetap_syn,theta0(1),v,A,sigma,dt);

    % save data
    folder_name = "data/wave_"+num2str(i);
    if exist(folder_name) < 7
        mkdir(folder_name)
    end
    fullFilePath_theta0 = fullfile(folder_name,"theta0.csv");
    fullFilePath_sigma = fullfile(folder_name,"sigma.csv");
    fullFilePath_A = fullfile(folder_name,"A.csv");
    fullFilePath_v = fullfile(folder_name,"v.csv");
    writematrix(theta0(1),fullFilePath_theta0);
    writematrix(sigma,fullFilePath_sigma);
    writematrix(A,fullFilePath_A);
    writematrix(v,fullFilePath_v);
end

% Add subtraction
XT_syn_tot = XT_syn + XT_subtraction;


%% Call Checker
ep = checker(XT,XT_syn_tot,1);

%% Plot
% Cleaned XT Diagram
figure()
set(gcf, 'Position', [200 200 2500 600])
subplot('Position', [.1 .3 .8 .6])
imagesc(t, thetap, XT_cleaned)
set(gca, 'Ydir', 'Normal')
title(['Run ', num]);
xlabel('Time [s]');
ylabel('$\theta$');
axis([ t(1) t(1)+300/fps 0 max(thetap)])
% formatPlot(gca,20)
subplot('Position', [.1 .12 .8 .03])
hold on
imagesc(t,thetap, XT_cleaned)
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
imagesc(t_syn, thetap_syn, XT_cleaned-XT_syn)
set(gca, 'Ydir', 'Normal')
title(['Run ', num]);
xlabel('Time [s]');
ylabel('$\theta$');
axis([ t_syn(1) t_syn(1)+300/fps 0 max(thetap_syn)])
% formatPlot(gca,20)
subplot('Position', [.1 .12 .8 .03])
hold on
imagesc(t_syn,thetap_syn,XT_cleaned-XT_syn)
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
plot(t,XT_cleaned(60,:),'LineWidth',2)
hold on
plot(t,XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Recreation")
xlim([t(1),t(1)+100*T/Nfr])

subplot(1,3,2)
plot(t,XT_cleaned(60,:),'LineWidth',2)
hold on
plot(t,XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Recreation")
xlim([t(floor(Nfr/2)),t(floor(Nfr/2))+100*T/Nfr])

subplot(1,3,3)
plot(t,XT_cleaned(60,:),'LineWidth',2)
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
plot(t,XT_cleaned(60,:),'LineWidth',2)
hold on
plot(t,XT_cleaned(60,:)-XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Subtraction")
xlim([t(1),t(1)+100*T/Nfr])

subplot(1,3,2)
plot(t,XT_cleaned(60,:),'LineWidth',2)
hold on
plot(t,XT_cleaned(60,:)-XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Subtraction")
xlim([t(floor(Nfr/2)),t(floor(Nfr/2))+100*T/Nfr])

subplot(1,3,3)
plot(t,XT_cleaned(60,:),'LineWidth',2)
hold on
plot(t,XT_cleaned(60,:)-XT_syn(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Subtraction")
xlim([t(end)-100*T/Nfr,t(end)])


% Cleared Subtraction
XT_cleared = XT_cleaned-100*XT_syn;
XT_cleared(XT_cleared<0) = 0;

figure()
set(gcf, 'Position', [200 200 2500 600])

subplot(1,3,1)
plot(t,XT_cleaned(60,:),'LineWidth',2)
hold on
plot(t,XT_cleared(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Cleared")
xlim([t(1),t(1)+100*T/Nfr])

subplot(1,3,2)
plot(t,XT_cleaned(60,:),'LineWidth',2)
hold on
plot(t,XT_cleared(60,:),'LineWidth',2)
hold off
xlabel('Time [s]');
ylabel('Amplitude');
legend("XT Data","Cleared")
xlim([t(floor(Nfr/2)),t(floor(Nfr/2))+100*T/Nfr])

subplot(1,3,3)
plot(t,XT_cleaned(60,:),'LineWidth',2)
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
plot(thetap,XT_cleaned(:,1),thetap,XT_syn(:,1),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")

subplot(2,2,2)
plot(thetap,XT_cleaned(:,floor(Nfr/4)),thetap,XT_syn(:,floor(Nfr/4)),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")

subplot(2,2,3)
plot(thetap,XT_cleaned(:,2*floor(Nfr/4)),thetap,XT_syn(:,2*floor(Nfr/4)),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")

subplot(2,2,4)
plot(thetap,XT_cleaned(:,3*floor(Nfr/4)),thetap,XT_syn(:,3*floor(Nfr/4)),'LineWidth',3)
xlabel('Theta [rad]');
ylabel('Amplitude');
legend("XT Data","Recreation")

%% Helper Functions
function XT_syn = add_wave(XT_syn,Nfr,thetap_syn,theta0,v,A,sigma,dt)
    % first wave
    gs = periodicGaussian(thetap_syn,theta0,A(1),sigma(1));
    XT_syn(:,1) = XT_syn(:,1) + gs';

    % subsequent waves
    t_dummy = linspace(1,Nfr,length(A));
    for i = 2:Nfr
        % interpolate
        A_it = interp1(t_dummy,A,i);
        sigma_it = interp1(t_dummy,sigma,i);
        v_it = interp1(t_dummy,v,i-1);
        
        % calc new theta0
        theta0 = theta0+v_it*dt;

        % generate gaussian
        gs = periodicGaussian(thetap_syn,theta0,A_it,sigma_it);
    
        % Update XT_syn
        XT_syn(:,i) = XT_syn(:,i)+gs';
    end
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