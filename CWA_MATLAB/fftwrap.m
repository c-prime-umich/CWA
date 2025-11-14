function [ f, P, phi ] = fftwrap( Hz, xIn )

% a wrapping function for matlab's fft that gives you the 1 sided fourier
% spectra along with its phase information

% Inputs:
% variable name  | meaning       | units
% Hz             | Sampling rate | Hertz
% x              | signal        | 

% Outputs
% variable name  | meaning                | units
% f              | frequency of transform | Hertz
% P              | amplitude of transform | 
% phi            | phase of transform     | 


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

