syms pr pt ptr q r xt xr kt kr t m;
sym t real; % No conjugate for transpose
P = [pt, ptr; ptr, pr];
Q = [0, 0; 0, q];
F = [1, t; 0, 1];
H = [1, 0];
x = [xt; xr]; K = [kt; kr]; y = [m; 0];
% Predict
xn1 = F * x
Pn1 = F * P * F' + Q
% Update
Kn = P*H'*(H*P*H'+r)^-1
xn = x + K*(m - H*x)
Pn = (eye(2) - K * H)*P
% Pn doesn't look symmetric, but numerically it works.
clear
P = [100, 0; 0, 16];
Q = [0, 0; 0, 0.25];
r = 2.5; t = 5;
F = [1, t; 0, 1]; H = [1, 0];
x = [14; 0];
for m = [19.70, 20.35, 20.09, 21.04, 17.79, 21.01, 22.25, ...
         22.91, 25.54, 29.61, 30.38, 30.28, 33.73, 35.71]
  y = [m; 0];
  P = F * P * F' + Q;
  K = P*H'*(H*P*H'+r)^-1;
  x = x + K*(m - H*x);
  P = (eye(2) - K*H)*P;
end