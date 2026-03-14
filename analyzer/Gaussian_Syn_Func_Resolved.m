function XT_syn = Gaussian_Syn_Func_Resolved(Nb,A,sigma,xc)
% XT Recreation via Gaussian wit resolved time steping
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

%% Build Gaussian
L = 2*pi;
    
XT_syn = periodicGaussian(thetap_syn,xc,A,sigma)';

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

end