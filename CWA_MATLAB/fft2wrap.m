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

