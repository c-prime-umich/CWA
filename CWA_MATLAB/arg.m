function [ phi ] = arg( z )

% returns polar angle, phi, of complex number z in radians

x = real(z);

y = imag(z);

phi = x;

N = numel(z);

for i = 1:N

    if x(i)>=0 && y(i)>=0 
        phi(i) = atan(y(i)/ x(i));
    elseif x(i)>=0 && y(i)<0
        phi(i) = atan(y(i)/ x(i)) + 2*pi;
    elseif x(i)<0 && y(i)>0
        phi(i) = atan(y(i)/ x(i)) + pi;
    elseif x(i)<0 && y(i)<0
        phi(i) = atan(y(i)/ x(i)) + pi;
    end
    
end

end

