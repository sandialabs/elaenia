syms m r
sym t real; % No conjugate for transpose
sym m real;
% State variance matrix
P = sym('P', [3 3]);
dt = 1;
% Process variance matrix (dt = 1)
Q = [0.25*dt^4, 0.5*dt^3, 0.5*dt^2;
     0.5*dt^3,  1*dt^2,   1*dt;
     0.5*dt^2,  1*dt,     1];
% State transition matrix
F = [1, dt, 0.5 * dt^2;
    0, 1, dt;
    0, 0, 1];
R = [r];
% Measurement matrix (map from measurements -> state)
H = [1, 0, 0];
% estimated state, Kalman gain, measurement variables
x = sym('x', [3 1]);
K = sym('K', [3 1]);
z = [m];
y = z - H*x;
% Predict
xn = F * x
Pn = F * P * F' + Q
% Update
yn = z - H*x
Kn = P*H'*(H*P*H'+R)^-1
xnn = x + K*y
eyekh = eye(3) - K * H % To simplify C
Pn   = (eye(3) - K * H)*P;

clear x m
% Now, do this numerically
P = [25, 0,  0;
    0,  10,  0;
    0,    0, 1];
R = 16.0; % Since we only track position, noise covariance is scalar
x = [20.0; 0; 0];
for m = [10.32053, 17.34839, 31.04178, 34.21409, 36.34723, ...
         29.81774, 28.00129, 41.06721, 37.83178, 42.29896, ...
         55.64220, 50.47855, 52.23186, 60.42627]
  % (trivially) transform measurements
  z = m;
  % Predict
  x = F*x;
  P = F * P * F' + Q;
  % Update
  y = z - H*x;
  K = P*H'*(H*P*H'+R)^-1;
  x = x + K*y;
  P = (eye(3) - K*H)*P;
end