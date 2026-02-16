function XT_syn = Gaussian_Syn_Func(fps,Nb,v,A,sigma,xc,Nt)
% XT Recreation via Gaussian
% Author: Timothy J. Welch

% Use the 9 provided Gaussian parameters to synthesize an XTdiagram
% Inputs:
%   p = [A1,sigma1,xc1,A2,sigma2,xc2,A3,sigma3,xc3]
%       xc      - initial center of Gaussian
%       A       - magnitude multiplier
%       sigma   - RMS width

%% Create Synthetic Data
dth_syn = 2*pi/Nb;
thetap_syn = 0:dth_syn:2*pi-dth_syn;
XT_syn = zeros(Nb,Nt+1);

%% Advect Gaussian
% Parameters for advection
dt = fps;
L = 2*pi;

% advect Gaussians
for it = 1:Nt+1
    [gs,xc] = advectGaussian_step(thetap_syn,v,A,sigma,xc,dt);

    % Update XT_syn
    XT_syn(:,it) = gs;
end

%% Helper Functions
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

function [gx,xc] = advectGaussian_step(theta,v,A,sigma,xc,dt)
    % v NEEDS to be in [rad/s]

    % update center using velocity
    xc = xc + v*dt;

    % wrap to periodic domain
    L = 2*pi;
    xc = mod(xc,L);

    % compute Gaussian shape at this time
    gx = periodicGaussian(theta,xc,A,sigma);
end

end