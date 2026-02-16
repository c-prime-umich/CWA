% XT Recreation Checker

% Author: Timothy J. Welch

% INPUTS:
%   XT:         Original XT data minus constant background
%   XT_syn:     Recreated XT data
%   VERBOSE:    Boolean to display epsilon
%
% OUTPUTS:
%   ep:         epsilon, the L1 norm of the difference

function ep = checker(XT,XT_syn,VERBOSE)

XT_energy = sum(abs(XT),"all");

% L1 norm
diff = XT_syn - XT;
ep = sum(abs(diff),"all")/XT_energy;

if VERBOSE
    fprintf('residual energy fraction = %.3e\n', ep);
end

end