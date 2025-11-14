function [ x, y ] = intersect2( l1, l2 )
% inputs are row vectors in the follow format [x0 y0 xhat yhat]. This is a
% line in point slope form with xhat and yhat constituting a unit vector

k = (l1(1)-l2(1)+l1(3)*(l2(2)-l1(2))/l1(4))/(l2(3)-l1(3)*l2(4)/l1(4));
x = l2(1) + k*l2(3);
y = l2(2) + k*l2(4);

end

