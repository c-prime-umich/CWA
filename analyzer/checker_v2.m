% XT Recreation Checker for C Conversion

% Author: Timothy J. Welch

% INPUTS:
%   XT.csv:         Original XT data
%   XT_bg.csv:      Background XT data
%   wave_n:         Directory for nth wave containing:
%       A.csv:      Amplitudes over time
%       sigma.csv:  gaussian widths over time
%       theta0.csv: initial radial position
%       v.csv:      velocities over time
%       t.csv:      time
%
% OUTPUTS:
%   ep:             epsilon, the L1 norm of the difference

clc; clear; close all;

%% Load XT
XT = readmatrix("data/XT.csv");
XT_bg = readmatrix("data/XT_bg.csv");

[Nb,Nfr] = size(XT);
L = 2*pi;
dth = 2*pi/Nb;
theta = (0:dth:2*pi-dth)';

XT_syn = XT_bg;

%% Loop over all waves
i = 1;
while 1
    % set dir
    fname = "data/wave_"+num2str(i);
    if exist(fname) > 6
        % extract data
        A = readmatrix(fname+"/A.csv");
        sigma = readmatrix(fname+"/sigma.csv");
        theta0 = readmatrix(fname+"/theta0.csv");
        v = readmatrix(fname+"/v.csv");
        t = readmatrix(fname+"/t.csv");

        % process
        t_full = linspace(t(1),t(end),Nfr);
        dt = t_full(2)-t_full(1);

        % add wave
        dx = theta - theta0;
        dx = mod(dx + L/2, L) - L/2;
        XT_syn(:,1) = XT_syn(:,1) + A(1)*exp(-dx.^2/(2*sigma(1)^2)); % initial wave
        for it=2:Nfr
            % interpolate parameters
            t_it = t_full(it);
            A_it = interp(t,A,t_it);
            sigma_it = interp(t,sigma,t_it);
            v_it = interp(t,v,t_it);

            % updata theta0
            theta0 = theta0 + v_it*dt;
            theta0 = mod(theta0,L);

            % add gaussian
            dx = theta - theta0;
            dx = mod(dx + L/2, L) - L/2;
            XT_syn(:,it) = XT_syn(:,it) + A_it*exp(-dx.^2/(2*sigma_it^2));
        end
    else
        break
    end
    i = i+1;
end

%% Calculate energy residual
XT_energy = sum(abs(XT),"all");

% L1 norm
diff = XT_syn - XT;
ep = sum(abs(diff),"all")/XT_energy;

fprintf('residual energy fraction = %.3e\n', ep);

% figure()
% set(gcf, 'Position', [200 200 2500 600])
% subplot('Position', [.1 .3 .8 .6])
% imagesc(t_full, theta, XT_syn-XT_bg)
% set(gca, 'Ydir', 'Normal')
% xlabel('Time [s]');
% ylabel('$\theta$');
% axis([ t_full(1) t_full(1)+300*dt 0 max(theta)])
% subplot('Position', [.1 .12 .8 .03])
% hold on
% imagesc(t_full,theta,XT_syn-XT_bg)
% plot([t_full(1) t_full(1)], [0 2*pi], 'r-', 'LineWidth', 3)
% plot([t_full(301) t_full(301)], [0 2*pi], 'r-', 'LineWidth', 3)
% hold off
% axis([t_full(1) t_full(end) 0 max(theta)])
% set(gcf,'PaperPositionMode','auto')
% set(gca, 'YColor', 'none')
% set(gcf,'color','w');

function vq = interp(x,v,xq)
    if xq <= x(1)
        vq = v(1);
    elseif xq >= x(end)
        vq = v(end);
    end
    for j=1:length(x)-1
        if (xq >= x(j) && xq <= x(j+1))
            t = (xq-x(j))/(x(j+1)-x(j));
            vq = v(j)+t*(v(j+1)-v(j));
        end
    end
end