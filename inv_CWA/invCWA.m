%% Inverse CWA

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

% Plot
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

%% plot4 Testing 1
load("plotData.mat")

% Data Extraction
t  = plot4.ttp(:);
vd = plot4.vdets(:);
vc = plot4.vcdets(:);
vr = plot4.vcrwps(:);
Id = plot4.detins(:);
Ic = plot4.cdetins(:);
Ir = plot4.crwpins(:);
x_det = cumtrapz(t, vd);
x_cdet = cumtrapz(t, vc);
x_crwp = cumtrapz(t, vr);

% set x grid (in x/D_CJ) and resolution
margin = 0.1*(max([x_det;x_cdet;x_crwp]) - min([x_det;x_cdet;x_crwp]) + 1e-6);
xvec = linspace(min([x_det;x_cdet;x_crwp]) - margin, ...
                max([x_det;x_cdet;x_crwp]) + margin, 400);
Nt = numel(t);
Nx = numel(xvec);

% choose kernel width (sigma in x units)
sigma = 0.2;    % tune: smaller = sharper tracks, larger = thicker bands

% --- build intensity matrix (rows: time, cols: x) ---
XT = zeros(Nt, Nx);
for k = 1:Nt
    % amplitudes: convert log-intensity to linear; if intens are already linear, skip exp()
    a_d = exp(Id(k));   a_c = exp(Ic(k));   a_r = exp(Ir(k));
    % normalize optionally
    % a_d = a_d / max([exp(Id); exp(Ic); exp(Ir)]); etc.

    % add Gaussian bumps centered at x positions at time k
    XT(k,:) = XT(k,:) + a_d * exp(-(xvec - x_det(k)).^2 / (2*sigma^2));
    XT(k,:) = XT(k,:) + a_c * exp(-(xvec - x_cdet(k)).^2 / (2*sigma^2));
    XT(k,:) = XT(k,:) + a_r * exp(-(xvec - x_crwp(k)).^2 / (2*sigma^2));
end

% --- display x-t image ---
figure;
imagesc(t, xvec, XT)
set(gca,'YDir','normal') % or 'reverse' if you want time downward
ylabel('x / D_{CJ}');
xlabel('t [s]');
title('Reconstructed x–t intensity map from plot4');
colorbar;
colormap(jet);
axis tight;

% --- optional: overlay trajectories ---
hold on;
plot(t, x_det,'-k','LineWidth',1.2)
plot(t, x_cdet,'-r','LineWidth',1.0)
plot(t, x_crwp,'-b','LineWidth',1.0)
hold off;


%% plot3 Attempt
s = plot3.a(:);    % projection coordinate (radon s)
projections = plot3.lights_psa;  % size: nproj x length(s)  (or transpose - check dims)
[nproj, ns] = size(projections);
% If projections is  length(s) x nproj, transpose it
if size(projections,2) == numel(s)
    projections = projections';
end

% --- assume theta if not present ---
if isfield(plot3,'theta')
    theta = plot3.theta(:);
else
    theta = linspace(-90, 90, nproj);  % best-guess; change if you know true angles
end

% --- reconstruct (choose output size) ---
Nout = 256;
R = iradon(projections, theta, 'linear', 'Ram-Lak', 1, Nout);

% --- display the reconstructed 2D field ---
figure;
imagesc(linspace(min(s), max(s), size(R,2)), linspace(min(theta), max(theta), size(R,1)), R)
xlabel('s (a or x/D_{CJ})');
ylabel('theta (deg)');
title('Backprojected/iradon reconstruction (interpret axes carefully)');
colorbar;
