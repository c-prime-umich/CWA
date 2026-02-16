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
% L1 norm
diff = XT_syn - XT;
ep = sum(abs(diff),"all");

if VERBOSE
    fprintf('epsilon = %.3e\n', ep);
end

end