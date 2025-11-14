function [plot1,plot2,plot3,plot4,ftpsave,PSD,PSTA] = CWA(XTStruct, XTStruct_full, phi, Dm, times, dat)
% CWA - Streamlined and commented

% Authors: Fabian Chacon and Mirko Gamba,
% edited and refactored by Timothy J. Welch

% Inputs:
%   XTStruct        - struct for short XT reader (used by XTReader_mod)
%                     This has three fields:
%                       XTdata :  NbxNfr double, input data,
%                           Nfr = number of frames (e.g., 5000),
%                           Nb = each frame is Nb (e.g., 101) points around the ring
%                       fps : frames per second
%                       t0 : 1xNfr or 1x1, the initial time
%   XTStruct_full   - full XT reader struct (for time-resolved analysis)
%                     Similar to XTStruct, but may have much larger Nfr
%                     Note: XTStruct is used for phase-shift analysis,
%                           XTStruct_full is used for the time analysis
%   phi             - equivalence ratio (fuel/air ratio), used for interpolation
%   Dm              - RDC mean diameter [in] (converted to [m])
%   times           - steady operating time window for run [s]
%   dat             - matrix used to lookup Ucj (first and ninth columns expected)

% Outputs:
%   plot1           - struct for plotting 2D Fourier Transform
%                     4 fields:
%                       fs : 1xNb double, spatial modes
%                       ft : 1x(Nfr-1) double, frequencies
%                       Plight : (Nfr-1)xNb double, 2D fourier shift of XTdata
%                       lim2 : 1x1 double, color limits for plotting Plight
%   plot2           - struct for plotting GSFS
%                     3 fields:
%                       f_fD : nFreqBinsx1 double, frequency / reference frequency
%                           nFreqBins = min(2500,floor(Nfr/2))
%                       a_Ucj : 1x401 double, phase shift scan parameter /
%                                             characteristic spead
%                       ftp : 401xnFreqBins, Fourier transform power (color for plot)
%   plot3           - struct for plotting Radon curves
%                     2 fields:
%                       a : 401x1 double, phase shift scan parameter
%                                         (velocity normalized by detonation speed)
%                       lights_psa : waveLx401 double, Radon transform
%                           waveL = 6 (number of waves examined)
%   plot4           - struct for plotting wave strengths
%                     11 fields
%                       intens : 1x(3*Ntp) double, intensities of all tracked waves
%                       detins : 1xNtp double, detonation-wave intensities
%                       cdetins : 1xNtp double, convected detonation component intensity
%                       crwpins : 1xNtp double, co-rotating wave intensity
%                       maxI : 1x1 double, global max intensity bound
%                       minI : 1x1 double, global min intensity bound
%                       ttp : 1xNtp double, time at each measurement
%                       vdets : 1xNtp double, normalized detonation wave speeds
%                       cvdets : 1xNtp double, convected detonation speed
%                       vcrwps : 1xNtp double, co-rotating wave speed
%                       Ntp : 1x1 double, floor(Nfr_full/71)
%   ftpsave         - plot2 data for saving
%   PSD             - Phase-Shifted Analysis data for saving
%   PSTA            - Struct of Phase-Shifted Time Analysis data for saving

%% --- Pre-initialize all outputs ---
plot1 = struct('fs', [], 'ft', [], 'Plight', [], 'lim2', []);
plot2 = struct('f_fD', [], 'a_Ucj', [], 'ftp', []);
plot3 = struct('a', [], 'lights_psa', []);
plot4 = struct('intens', [], 'detins', [], 'cdetins', [], 'crwpins', [], ...
               'maxI', [], 'minI', [], 'ttp', [], 'vdets', [], 'vcdets', [], ...
               'vcrwps', [], 'Ntp', []);
ftpsave = [];
PSD     = [];
PSTA    = struct('ttp', [], 'vdets', [], 'detins', [], 'vcdets', [], ...
                 'cdetins', [], 'vcrwps', [], 'crwpins', [], ...
                 'Ndets', [], 'lights_t', [], 'a_tr', []);


%% ----- Basic derived parameters and checks -----
% Interpolate Ucj from provided dat (CodeGen-safe: dat must be regular numeric)
Ucj = interp1(dat(:,1), dat(:,9), phi); % [m/s]

% Convert diameter to meters for frequency normalization
Cd = Dm * pi * 0.0254;   % circumference [m]

% Non-dimensional frequency scale factor used later
fD = Ucj / Cd;

% Read a XT block
[ t_short, ~, lights_short, fps, Nb ] = XTReader_mod(XTStruct);

if isempty(t_short) || isnan(t_short(1))
    % Early exit on invalid input
    return
end

lights_short = lights_short';  % match expected orientation
lights_short(isnan(lights_short)) = 1;

% Limit to requested time window (times)
ff = round(1 + (max([t_short(1) times(1)]) - t_short(1))*fps);
lf = round(1 + (min([t_short(end) times(2)]) - t_short(1))*fps);
lf = min(lf, length(lights_short));

lights_short = lights_short(ff:lf, :);
[Nshort, ~] = size(lights_short);
lights_short(isnan(lights_short)) = 1;

%% ----- Video 2D Spectrum -> compute Plight and normalized ft -----
% FFT over spatial index
[ Plight_raw, fs, ft] = fft2wrap(lights_short, Nb, fps);
Plight = log(abs(Plight_raw));
ft = ft/fD;
lim2 = max(max(Plight(:,round((Nb-1)/2):end)));

% Save plot1 variables
plot1.fs = fs;
plot1.ft = ft;
plot1.Plight = Plight;
plot1.lim2 = lim2;

% quick guard
if isempty(Plight)
    return
end

% Subtract mean (detrend spatially) for phase-shift processing
lights_short = lights_short - mean(mean(lights_short));

%% ----- Phase shift sweep (single-block) -----
% 'a' is phase shift scan parameter (units of velocity*magnitude)
a = -4000:20:4000;
Npic = min([5000 Nshort]);
if mod(Npic,2) == 0
    Npic = Npic - 1;
end

% Preallocate ftps array: length(a) x freqBins x Nb
nFreqBins = (Npic-1)/2 + 1;
ftps = zeros(length(a), nFreqBins, Nb);

% Prepare spatial sampling vector used for interpolation of phase shift
vecb = linspace(0, Cd, Nb);

% For each candidate phase shift a(j), shift spatial samples and FFT temporally
for j = 1:length(a)
    % Preallocate values matrix for this a (time x sensor)
    vals = zeros(Npic, Nb);
    for k = 1:Npic
        % Compute phase-shifted sample positions for row k
        phish = a(j)*(k-1)/fps + Cd*(0:Nb-1)/Nb;
        phish = phish - Cd*floor(phish/Cd);          % wrap to [0,Cd)
        % Interpolate from the measured sensors (spatial interpolation)
        vals(k, :) = interp1(vecb, lights_short(k, :), phish);
    end

    % FFT in time for each sensor column
    for p = 1:Nb
        [f, P, ~] = fftwrap(fps, vals(:, p));
        ftps(j, :, p) = P;
    end
end

% Collapse over sensors (max across sensor index)
ftp = max(ftps, [], 3);

% Save ftpsave array: [0 f'/fD; a'/Ucj ftp]
ftpsave = [0 f'/fD; a'/Ucj ftp];

% plot2 variables
plot2.f_fD = f / fD; % frequency over reference frequency
plot2.a_Ucj = a / Ucj; % 
plot2.ftp = ftp;

%% --- PhaseShiftAnalysis (single block) ---
% Parse ftpsave into matrices for analysis
f = ftpsave(1, 2:end);
a = ftpsave(2:end, 1);
ftp_mat = ftpsave(2:end, 2:end);

df = f(2) - f(1);
da = a(2) - a(1);

% Useful indices for later windowing (kept from original algorithm)
[~, I0] = min(abs(a - 2));
[~, I1] = min(abs(a - 3));
[~, I2] = min(abs(a + 1));
[~, I3] = min(abs(a - 1));
[~, I4] = min(abs(f - 0.08));
[~, I5] = min(abs(a - 0.2));
[~, I6] = min(abs(a + 0.2));
I8 = (a(2)-a(1))/(f(2)-f(1));
[~, I9] = min(abs(f - 0.02));

% Background subtraction: subtract minimum across rows (freq) from each row
[X, ~] = size(ftp);
s = min(ftp,[],1);
background = ftp;
for j = 1:X
    background(j,:) = s;
end
ftpnew = ftp - background;

% Phase-shift based lights estimate
waveL = 6;
lights_psa = zeros(waveL, length(a));

% Calculate a0
a0 = round(length(a)/2);

% Midpoint grid for frequency and a to perform integration along lines (as in original)
bf = f(1:end-1) + 0.5*df;
ba = a(1:end-1) + 0.5*da;
% Assemble segment parameter arrays for intersection routine
bf_ext = [bf' zeros(length(bf),1) zeros(length(bf),1) ones(length(bf),1)];
ba_ext = [zeros(length(ba),1) ba ones(length(ba),1) zeros(length(ba),1)];

for n = 1:waveL
    % unit direction vectors (positive and negative slope)
    mLp = [n 1] / norm([n 1]);
    mLm = [n -1] / norm([n -1]);

    for j = 1:length(a)
        pos = [0 a(j) mLp];
        neg = [0 a(j) mLm];

        % Collect intersection points between pos/neg rays and bf/ba segment sets
        % Preallocate locs (maximum possible hits)
        Nloc = 2 * length(bf) + length(ba) + 1;
        locs = zeros(Nloc, 2);
        cnt = 1;

        for k = 1:length(bf)
            [x, y] = intersect2(pos, bf_ext(k,:));
            locs(cnt, :) = [x y];
            cnt = cnt + 1;
            [x, y] = intersect2(neg, bf_ext(k,:));
            locs(cnt, :) = [x y];
            cnt = cnt + 1;
        end
        for k = 1:length(ba)
            if ba(k) > a(j)
                [x, y] = intersect2(pos, ba_ext(k,:));
            else
                [x, y] = intersect2(neg, ba_ext(k,:));
            end
            locs(cnt, :) = [x y];
            cnt = cnt + 1;
        end
        locs(cnt, :) = [0 a(j)];

        % Sort by 'y' (a) coordinate and trim to range
        [~, I] = sort(locs(:,2));
        locs = locs(I, :);
        tar = locs(:,1) < f(end);
        locs = locs(tar,:);
        tar = locs(:,2) > a(1);
        locs = locs(tar,:);
        tar = locs(:,2) < a(end);
        locs = locs(tar,:);

        % Integrate FTP along successive segment midpoints
        counts = 0;
        for k = 1:(size(locs,1)-1)
            dis = norm(locs(k,:) - locs(k+1,:));
            mid = 0.5*(locs(k,:) + locs(k+1,:));
            [~, If] = min(abs(mid(1) - f));
            [~, Ia] = min(abs(mid(2) - a));
            counts = counts + dis * ftpnew(Ia, If);
        end

        lights_psa(n, j) = counts;
    end

    % Baseline subtraction per n to remove local minima contributions
    amin = a;
    lightsmin = lights_psa(n, :);
    for j = 2:(length(a)-1)
        if (lights_psa(n, j) > lights_psa(n, j+1)) || (lights_psa(n, j) > lights_psa(n, j-1))
            lightsmin(j) = 0;
        end
    end
    [lightsmin_sorted, I] = sort(lightsmin);
    amin = amin(I);
    startIdx = sum(lightsmin_sorted == 0) + 1;
    amin = amin(startIdx:end);
    lightsmin = lightsmin(startIdx:end);
    lightsoff = interp1(amin, lightsmin, a)';
    lights_psa(n, :) = lights_psa(n, :) - lightsoff;
end

% Save PSA summary
plot3.a = a;
plot3.lights_psa = lights_psa;

%% ----- Post-process PSA results to find detectors and rwp -----
% Mask central small region and apply thresholds (mirrors original logic)
lights_mod = lights_psa;
lights_mod(:, I6:I5) = 0;       % remove DC region
maxL = max(lights_mod(:));
if maxL == 0
    maxL = 1;
end
background_thresh = 5 * rms(lights_mod(3, I0:I1)) / maxL;

lights_mod(:, 1:I2) = 0;
lights_mod(:, I3:end) = 0;
for j = waveL:-1:1
    lights_mod(j,:) = lights_mod(j,:) / maxL;
end
lights_mod(lights_mod < background_thresh) = 0;

maxes = max(lights_mod, [], 2);
[~, detn] = max(maxes);
detL = 1 / detn;
[~, Idet] = max(lights_mod(detn, :));

% Quadratic interpolation around peak to get sub-bin velocity estimate
if Idet == 1
    vdet = 0;
else
    p = polyfit(a(Idet-1:Idet+1)', lights_mod(detn,Idet-1:Idet+1), 2);
    vdet = - p(2) / 2 / p(1);
end

detin = sum(ftpnew(Idet, 1:I4));

if vdet > 0
    lights_mod(:,a0:end) = 0;
else
    lights_mod(:,1:a0) = 0;
end

[v, Icdet] = max(lights_mod(detn,:));

% Co-rotating detection (second peak)
if v > 0
    p = polyfit(a(Icdet-1:Icdet+1)', lights_mod(detn,Icdet-1:Icdet+1), 2);
    vcdet = - p(2) / 2 / p(1);

    cdetL = detL;
    cdetin = sum(ftpnew(Icdet,1:I4));
else
    vcdet = 0;
    cdetL = 0;
    cdetin = 0;
end

[v, Icrwp] = max(lights_mod(2,:));

if v > 0
    p = polyfit(a(Icrwp-1:Icrwp+1)', lights_mod(2,Icrwp-1:Icrwp+1), 2);
    vcrwp = - p(2) / 2 / p(1);

    crwpL = 2;
    crwpin = sum(ftpnew(Icrwp,1:I4));
else
    vcrwp = 0;
    crwpL = 0;
    crwpin = 0;
end

% Make PSD summary vector to match original layout
PSD = [detin, vdet, detL, cdetin, vcdet, cdetL, crwpin, vcrwp, crwpL, mean(rms(lights_short,2))];

%% ----- PhaseShiftTimeAnalysis (time-resolved) -----
% Read full time series data
[ t_full, ~, lights_full, fps_full, Nb_full ] = XTReader_mod(XTStruct_full);
lights_full = lights_full';   % ensure orientation (time x sensors)
lights_full = lights_full - mean(mean(lights_full));

if isempty(t_full)
    return
end

% Parameters for time-resolved sweep
Vr = 150;
dv = 20;
a_tr = -3000:dv:3000;
Na = length(a_tr);

% Prepare for blocks of frames
Nfr = 71;
Ntp = floor(length(t_full) / Nfr);

% Preallocate accumulators for PSTA results
ftpsomega = zeros(Na, (Nfr-1)/2+1, Ntp);
vdets = zeros(1, Ntp);
detins = zeros(1, Ntp);
Ndets = zeros(1, Ntp);
vcdets = zeros(1, Ntp);
cdetins = zeros(1, Ntp);
vcrwps = zeros(1, Ntp);
crwpins = zeros(1, Ntp);
ttp = zeros(1, Ntp);

% Reusable vectors and preallocations for inner loops
vecb_full = linspace(0, Cd, Nb_full);
vals = zeros(Nfr, Nb_full);
ftps_block = zeros(Na, (Nfr-1)/2+1, Nb_full);

for m = 1:Ntp
    idxTime = (m-1)*Nfr + 1:m*Nfr;
    subxt = lights_full(idxTime, :);
    ttp(m) = mean(t_full(idxTime));

    % Interpolate each row to sensor-phase vector (spatial positions)
    inter = interp1(vecb_full, subxt', Cd.*(0:Nb_full-1)./Nb_full)';

    for j = 1:Na
        % compute wrapped phase shifts for block
        phishM = a_tr(j).*((1:Nfr)-1)' ./ fps_full + Cd.*(0:Nb_full-1)./Nb_full;
        phishM = phishM - Cd*floor(phishM./Cd);

        % determine integer shifts per row for circular shift (fast)
        [~, shiftIdx] = max(phishM, [], 2);

        % apply circshift row-wise according to shiftIdx
        for k = 1:Nfr
            vals(k, :) = circshift(inter(k, :), shiftIdx(k));
        end

        % FFT over time for each sensor column -> store power
        [~, P] = fftwrap(fps_full, vals);     % P: freqBins x Nb_full
        ftps_block(j, :, :) = P;
    end

    % Collapse across sensors (max) and store per time-block
    ftpsomega(:, :, m) = max(ftps_block, [], 3);
end

% Normalize axes for final time-resolved results
f = fftwrap(fps_full,vals);
f = f / fD;
a_tr = a_tr / Ucj;
a0 = round(Na/2);
Nf = length(f);

da = a_tr(2)-a_tr(1);
df = f(2)-f(1);

% Useful indices for later windowing (again?)
[~, I0] = min(abs(a_tr-1));
[~, I1] = min(abs(a_tr-1.5));
[~, I2] = min(abs(a_tr+1));
[~, I3] = min(abs(a_tr-1));
[~, I4] = min(abs(f-.08));
[~, I5] = min(abs(a_tr-.3));
[~, I6] = min(abs(a_tr+.3));
I9 = 0;

% Post-process each time block to find detection velocities (similar to PSA)
waveL = 5;
lights_t = zeros(waveL, Na, Ntp);
lights = zeros(waveL, Na);

% For intersect usage
bf = f(1:end-1) + .5*df;
ba = a_tr(1:end-1) + .5*da;
bf = [bf zeros(length(bf),1) zeros(length(bf),1) ones(length(bf),1)];
ba = [zeros(length(ba),1) ba' ones(length(ba),1) zeros(length(ba),1)];

% Build locs matrices and compute midpoints & distances as vectorized as possible
Nbf = length(bf);
Nba = length(ba);
Nlocs = 2*Nbf + Nba + 1;
inda0 = ba(:,2) <= a_tr;
ind3 = (2*Nbf+2)-1:(2*Nbf + Nba);

% Preallocate locsXM and locsYM
locs0XM = zeros(Nlocs,Na);
locs0YM = zeros(Nlocs,Na);

% Precompute background minima per block for subtraction
s0 = zeros((Nfr-1)/2+1,Ntp);
s0(:,:) = min(ftpsomega,[],1);
s0 = s0'; % Ntp x freqBins

% For use in loop
Mat1 = ones(Na,1);
fM = zeros(1,1,Nf);
fM(1,1,:) = f;
fM = repmat(fM,Nlocs,Na,1);

aM = zeros(1,1,Na);
aM(1,1,:) = a_tr;
aM = repmat(aM,Nlocs,Na);

for m = 1:Ntp
    ftp = ftpsomega(:, :, m);
    background = Mat1*s0(m,:);
    ftpnew = ftp - background;

    lights = 0.*lights;

    for n = 1:waveL
        mLp = [n 1] / norm([n 1]);
        mLm = [n -1] / norm([n -1]);

        posM = [zeros(Na,1) (a_tr(:)) ones(Na,1).*mLp(1) ones(Na,1).*mLp(2)];
        negM = [zeros(Na,1) (a_tr(:)) ones(Na,1).*mLm(1) ones(Na,1).*mLm(2)];

        [Xfp, Yfp] = intersect2vec(posM,bf);
        [Xfm, Yfm] = intersect2vec(negM,bf);
        [Xap, Yap] = intersect2vec(posM,ba);
        [Xam, Yam] = intersect2vec(negM,ba);

        % Choose proper intersections based on sign
        Xa = Xap;
        Xa(inda0) = Xam(inda0);
        Ya = Yap;
        Ya(inda0) = Yam(inda0);

        % Compose locsXM and locsYM
        locsXM = locs0XM;
        locsYM = locs0YM;

        locsXM(1:2:(1+2*(Nbf-1)), :) = Xfp;
        locsXM(2:2:2*Nbf, :) = Xfm;
        locsXM(ind3,:) = Xa;

        locsYM(1:2:(1+2*(Nbf-1)),:) = Yfp;
        locsYM(2:2:2*Nbf,:) = Yfm;
        locsYM(ind3,:) = Ya;
        locsYM(end,:) = a_tr;

        % Bound and sort per column
        tar1 = locsXM < f(end);
        tar2 = (locsYM > a_tr(1)) & (locsYM < a_tr(end));

        locsXM(~(tar1&tar2)) = NaN;
        locsYM(~(tar1&tar2)) = NaN;

        [locsYM,IM] = sort(locsYM,1,'MissingPlacement','last');

        locsXM = locsXM(sub2ind([Nlocs Na],IM,repmat(1:Na,Nlocs,1)));

        locs2XM = [locsXM(2:end,:); zeros(1,Na)];
        locs2YM = [locsYM(2:end,:); zeros(1,Na)];

        disMM = sqrt( (locsXM-locs2XM).^2 + (locsYM-locs2YM).^2 );
        disMM(isnan(disMM)) = 0;

        midXM = (locsXM+locs2XM)./2;
        midYM = (locsYM+locs2YM)./2;

        % Find nearest frequency and a bin indices
        [~,IfMM] = min(abs(midXM-fM),[],3);
        [~,IaMM] = min(abs(midYM-aM),[],3);

        indCM = (IfMM-1) .* Na + IaMM;
        % linear indexing into ftpnew (Na x nFreqBins) for vectorized multiplication
        countsM = ftpnew(indCM') * disMM; % element-wise
        lights(n,:) = diag(countsM)';

        % Local baseline removal per time-block (similar to PSA)
        if n > 1
            amin = a_tr;
            lightsmin = lights(n,:);

            lightsP = circshift(lights(n,:),-1);
            lightsM = circshift(lights(n,:),1);

            indM = lights(n,:) > lightsP | lights(n,:) > lightsM;
            indM(1) = false;
            indM(end) = false;

            lightsmin = lightsmin(~indM);
            amin = amin(~indM);

            lightsoff = interp1(amin,lightsmin,a_tr);

            lights(n,:) = lights(n,:) - lightsoff;

        else
            lights(n,:) = lights(n,:) - mean(lights(n,1:I1-I0));
        end


        lights(n,:) = lights(n,:) - min(lights(n,:)');

    end

    lights_t(:, :, m) = lights;

    % Mask and threshold similar to PSA flow
    lights(:, I6:I5) = 0; % eliminates the DC component
    background = 4 * rms(lights(2, I0:I1));
    lights(:, 1:I2) = 0; % removes anything above |Ucj|
    lights(:, I3:end) = 0; % removes anything above |Ucj|
    lights(lights < background) = 0; % background correction

    % Find detection peaks and quad-fit for velocity estimation
    maxes = max(lights,[],2);
    [~, detn] = max(maxes);
    [~, Idet] = max(lights(detn,:));
    if Idet <= 1
        vdets(m) = NaN;
        detins(m) = NaN;
        Ndets(m) = NaN;
        vcdets(m) = NaN;
        cdetins(m) = NaN;
        vcrwps(m) = NaN; 
        crwpins(m) = NaN;
    else
        del = floor(Vr / dv);
        p = quadFit(a_tr(Idet-del:Idet+del), lights(detn,Idet-del:Idet+del));
        vdets(m) = -p(2) / (2*p(1));
        Ndets(m) = detn;
        detins(m) = sum(ftpnew(Idet, 1:I4));

        if vdets(m) > 0 % no co-rotating waves
            lights(:,a0:end) = 0;
        else
            lights(:,1:a0) = 0;
        end

        [v1, Icdet] = max(lights(1, :));
        if v1 > 0
            p = quadFit(a_tr(Icdet-del:Icdet+del), lights(detn,Icdet-del:Icdet+del));
            vcdets(m) = -p(2) / (2*p(1));
            cdetins(m) = sum(ftpnew(Icdet, 1:I4));
        else
            vcdets(m) = NaN;
            cdetins(m) = NaN;
        end

        [v2, Icrwp] = max(lights(2, :));
        if v2 > 0
            p = quadFit(a_tr(Icrwp-del:Icrwp+del), lights(2,Icrwp-del:Icrwp+del));
            vcrwps(m) = -p(2) / (2*p(1));
            crwpins(m) = sum(ftpnew(Icrwp, 1:I4));
        else
            vcrwps(m) = NaN;
            crwpins(m) = NaN;
        end
    end
end

% Save PSTA results
PSTA.ttp = ttp;
PSTA.vdets = vdets;
PSTA.detins = detins;
PSTA.vcdets = vcdets;
PSTA.cdetins = cdetins;
PSTA.vcrwps = vcrwps;
PSTA.crwpins = crwpins;
PSTA.Ndets = Ndets;
PSTA.lights_t = lights_t;
PSTA.a_tr = a_tr;

% Save for Plot4
intens = [detins cdetins crwpins];

intens = log(intens);
detins = log(detins);
cdetins = log(cdetins);
crwpins = log(crwpins);

intens(isinf(intens)) = NaN;

maxI = max(intens, [],'omitnan');
minI = min(intens, [],'omitnan');

plot4.intens = intens;
plot4.detins = detins;
plot4.cdetins = cdetins;
plot4.crwpins = crwpins;
plot4.maxI = maxI;
plot4.minI = minI;
plot4.ttp = ttp;
plot4.vdets = vdets;
plot4.vcdets = vcdets;
plot4.vcrwps = vcrwps;
plot4.Ntp = Ntp;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% ----- End of main function -----

%% ----- Nested helper functions -----

    function p = quadFit(x, y)
        % quadFit  Solve quadratic coefficients [a;b;c] via linear algebra
        % using normal equations (fast and CodeGen-friendly).
        A = [sum(x.^4), sum(x.^3), sum(x.^2);
             sum(x.^3), sum(x.^2), sum(x);
             sum(x.^2), sum(x),    length(x)];
        B = [sum(x.^2 .* y); sum(x .* y); sum(y)];
        p = A \ B;
    end

    function [X, Y] = intersect2vec(L1, L2)
        % intersect2vec  Vectorized line-segment intersection handler
        % L1 and L2 are N x 4 matrices describing segments as [x0 y0 dx dy]
        % Returns X and Y matrices of intersections (size: rows(L1) x rows(L2))
        x1 = L1(:,1); y1 = L1(:,2);
        x2 = L2(:,1); y2 = L2(:,2);
        % Avoid zeros in direction comps to prevent divide-by-zero
        L1(L1(:,3)==0,3) = 1e-10;
        L1(L1(:,4)==0,4) = 1e-10;
        L2(L2(:,3)==0,3) = 1e-10;
        L2(L2(:,4)==0,4) = 1e-10;

        m1 = L1(:,4) ./ L1(:,3);
        m2 = L2(:,4) ./ L2(:,3);

        a1 = m1';
        a2 = m2;
        b1 = -1 .* ones(size(y1))';
        b2 = -1 .* ones(size(y2));
        c1 = (y1 - m1 .* x1)';
        c2 = (y2 - m2 .* x2);

        X = (b1.*c2-b2.*c1)./(a1.*b2-a2.*b1);
        Y = (a2.*c1-a1.*c2)./(a1.*b2-a2.*b1);
    end

end
