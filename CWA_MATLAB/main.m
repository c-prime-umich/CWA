%% CWA Tester

% Authors: Fabian Chacon and Mirko Gamba,
% edited and refactored by Timothy J. Welch

clc; clear; close all;

%% Set Directories and Select Data
XTdir = '/Users/tjwelch/Desktop/APCL/Research_Projects/Formal Verification/CWA_Local/XT Diagrams';
Savedir = '/Users/tjwelch/Desktop/APCL/Research_Projects/Formal Verification/CWA_Local/CWA Results';
Imgdir = '/Users/tjwelch/Desktop/APCL/Research_Projects/Formal Verification/CWA_Local/CWA Figures';

dat = readmatrix("H2AirDetProp.xlsx");

% run = 3423;
% phi = 0.59;          %run equivalence ratio

% run = 3426;
% phi = 0.85;          %run equivalence ratio

run = 3433;
phi = 1.46;          %run equivalence ratio

% run = 3443;
% phi = 0.81;          %run equivalence ratio


Dm = 5.76;          %RDC mean diameter [in]
Tair = 300;         %air temperature at inlet [K]
times = [6.8, 6.9]; %run steady operating time [s]


%% Read XT Diagram
ext='';
num = num2str(run,'%05.0f');
XTfile = [XTdir,'/Run_', num,'.mat'];
XTfile_full = [XTdir,'/Run_', num, '-full.mat'];
XTStruct = load(XTfile);
XTStruct_full = load(XTfile_full);

%% Run CWA
[plot1,plot2,plot3,plot4,ftpsave,PSD,PSTA] = CWA(XTStruct,XTStruct_full,phi,Dm,times,dat);

%% Plot 1 - 2D Fourier Transform
% Load variables
fs = plot1.fs;
ft = plot1.ft;
Plight = plot1.Plight;
lim2 = plot1.lim2;

% Plot
figure
imagesc(fs, ft, Plight) % frequency vs. spatial modes
set(gca, 'Ydir', 'Normal')
titl = title(['Run ', num]);
xlab = xlabel('$n_s$');
ylab = ylabel('$f/f{CJ}$');
axis([0 10 -5 5])
caxis([lim2-10 lim2])
colormap jet
fplot( [], xlab, ylab, titl, gca, 20 )

%% Plot 2 - Galilean-Shifted Fourier Spectrum (GSFS)
% 1D temporal Fourier transform that a point
% observer would compute in a frame of reference which
% is moving at a velocity v relative to the lab reference frame.

% Load variables
f_fD = plot2.f_fD;
a_Ucj = plot2.a_Ucj;
ftp = plot2.ftp;

% Plot
figure
imagesc( f_fD, a_Ucj, log(ftp)) % 
set(gca, 'Ydir', 'Normal')
titl = title(['Run ', num]);
xlab = xlabel('$f/f_{CJ}$');
ylab = ylabel('$v/D_{CJ}$');
axis([0 3 -2.5 2.5])
colormap jet
caxis([max(max(log(ftp)))-5 max(max(log(ftp)))])
fplot( [], xlab, ylab, titl, gca, 20 )

%% Plot 3 - Radon Curves
% Load variables
a = plot3.a;
lights = plot3.lights_psa;

% Plot
figure
hold on
plot(a, lights(1,:) / max(lights(:)), 'k-')
plot(a, lights(2,:) / max(lights(:)), 'r-')
plot(a, lights(3,:) / max(lights(:)), 'b-')
plot(a, lights(4,:) / max(lights(:)), 'g-')
plot(a, lights(5,:) / max(lights(:)), 'm-')
hold off
titl = title('');
xlab = xlabel('$v/D_{\mathrm{CJ}}$','Interpreter','latex');
ylab = ylabel('[a.u.]','Interpreter','latex');
leg = legend('$n$ = 1','$n$ = 2','$n$ = 3','$n$ = 4');
axis([-2.5 2.5 0 1.1])
fplot( leg, xlab, ylab, titl, gca, 24 )

%% Plot 4 - Strengths of waves over time
% color map tracking the wave strengths over the time window

% Load variables
cmap1 = jet(100);
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
Ntp = plot4.Ntp;

% Plot
if not(isnan(maxI) || isnan(minI))
    detinco = ceil(99 * (detins - minI) / (maxI-minI))+1;
    cdetinco = ceil(99 * (cdetins - minI) / (maxI-minI))+1;
    crwpinco = ceil(99 * (crwpins - minI) / (maxI-minI))+1;

    detinco(detinco>100) = 100;
    cdetinco(cdetinco>100) = 100;
    crwpinco(crwpinco>100) = 100;

    detcolor = zeros(Ntp,3);
    cdetcolor = zeros(Ntp,3);
    crwpcolor = zeros(Ntp,3);

    for j = 1:Ntp
        if isnan(detinco(j)) || isinf(detinco(j))
            detcolor(j,:) = [1 1 1];
        else
            detcolor(j,:) = cmap1(detinco(j),:);
        end
        if isnan(cdetinco(j)) || isinf(cdetinco(j))
            cdetcolor(j,:) = [1 1 1];
        else
            cdetcolor(j,:) = cmap1(cdetinco(j),:);
        end
        if isnan(crwpinco(j)) || isinf(crwpinco(j))
            crwpcolor(j,:) = [1 1 1];
        else
            crwpcolor(j,:) = cmap1(crwpinco(j),:);
        end
    end


    figure
    hold on
    scatter(ttp, vdets, 40, detcolor, 'filled', 'o')
    scatter(ttp, vcdets, 40, cdetcolor, 'filled', 's')
    scatter(ttp, vcrwps, 40, crwpcolor, 'filled', 'd')
    hold off
    axis([min(ttp)-.05 max(ttp)+.05 -1 1])
    xlab = xlabel('$t$ [s]');
    ylab = ylabel('$v/D_{CJ}$');
    titl = title(['Run ', num]);
    h = colorbar;
    ylabel(h, '$\textup{ln}(S)$', 'FontName', 'Times', 'FontSize', 20, 'interpreter', 'latex')
    colormap jet
    caxis([min(intens) max(intens)])
    fplot( [], xlab, ylab, titl, gca, 20 )
end