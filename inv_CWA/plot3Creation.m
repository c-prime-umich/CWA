%% Isolated section of code in which plot3 is generated

% For organization (not executable)

% Interpolate Ucj from provided dat
Ucj = interp1(dat(:,1), dat(:,9), phi); % [m/s]

% Convert diameter to meters for frequency normalization
Cd = Dm * pi * 0.0254;   % circumference [m]

% Non-dimensional frequency scale factor used later
fD = Ucj / Cd;

% Read a XT block
lights_short = XTStruct.XT;
t0 = XTStruct.t0;
fps = XTStruct.fps;

[ Nb, Nfr ] = size(lights_short);

dth = 2*pi/Nb;
thetap = 0:dth:2*pi-dth;

t_short = (0:Nfr-1)/fps + t0;

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

%% Functions
function [ f, P, phi ] = fftwrap( Hz, xIn )
[Nrow,Ncol] = size(xIn);

if Nrow==1 || Ncol == 1   
    if Nrow < Ncol %make it a column vector
        x = reshape(xIn,[],1);
    else
        x = xIn;
    end    
    L = length(x);
    if mod(L,2) == 1
        x = x(1:end-1);
        L = length(x);
    end    
else    
    L = Nrow;
    if mod(L,2)==1
        x = xIn(1:end-1,:);
        L = Nrow-1;   
    else
        x = xIn;
    end
end

if nargout == 1
    f = Hz*(0:(L/2))'/L;
    return
end

y = fft(x);
if nargout >= 3
    phi = arg(y);
    phi = phi(1:L/2+1,:);
end

P2 = abs(y/L);
P = P2(1:L/2+1,:);
P(2:end-1,:) = 2*P(2:end-1,:);

f = Hz*(0:(L/2))'/L;
end

function [ P, fx, fy ] = fft2wrap( x, Hzx, Hzy )
[Ny, Nx] = size(x);
if mod(Nx,2) == 0
    x = x(:,1:Nx-1);
    Nx = Nx - 1;
end

if mod(Ny,2) == 0
    x = x(1:Ny-1,:);
    Ny = Ny - 1;
end

fx = Hzx*(-(Nx-1)/2:(Nx-1)/2)/Nx;
fy = Hzy*(-(Ny-1)/2:(Ny-1)/2)/Ny;

P = fft2(x);
P = fftshift(P);

end