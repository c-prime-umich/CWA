%% Isolated section of code in which plot3 is generated

% For organization (not executable)

%%% To Recreate %%%
lights_full = XTStruct_full.XT;
t0 = XTStruct_full.t0;
fps_full = XTStruct_full.fps;
[Nb_full,Nfr] = size(lights_full);

dth = 2*pi/Nb_full;
thetap = 0:dth:2*pi-dth;

t_full = (0:Nfr-1)/fps_full + t0;
%%% End of "To Recreate" %%%


lights_full = lights_full';   % ensure orientation (time x sensors)
lights_full = lights_full - mean(mean(lights_full));

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
        % -- from fftwrap --
        [Nrow,Ncol] = size(vals);
        if Nrow==1 || Ncol == 1
            if Nrow < Ncol %make it a column vector
                x = reshape(vals,[],1);
            else
                x = vals;
            end
            L = length(x);
            if mod(L,2) == 1
                x = x(1:end-1);
                L = length(x);
            end   
        else   
            L = Nrow;
            if mod(L,2)==1
                x = vals(1:end-1,:);
                L = Nrow-1;  
            end
        end
        y = fft(x);
        P2 = abs(y/L);
        P = P2(1:L/2+1,:);
        P(2:end-1,:) = 2*P(2:end-1,:); % P: freqBins x Nb_full
        % -- End from fftwrap --
        ftps_block(j, :, :) = P;
    end

    % Collapse across sensors (max) and store per time-block
    ftpsomega(:, :, m) = max(ftps_block, [], 3);
end

% Normalize axes for final time-resolved results
% -- from fftwrap --
[Nrow,Ncol] = size(vals);
if Nrow==1 || Ncol == 1
    if Nrow < Ncol %make it a column vector
        x = reshape(vals,[],1);
    else
        x = vals;
    end
    L = length(x);
    if mod(L,2) == 1
        x = x(1:end-1);
        L = length(x);
    end   
else   
    L = Nrow;
    if mod(L,2)==1
        x = vals(1:end-1,:);
        L = Nrow-1;  
    end
end
% -- End from fftwrap --

f = fps_full*(0:(L/2))'/L;
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