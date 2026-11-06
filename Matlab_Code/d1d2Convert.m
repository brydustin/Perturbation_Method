 %{
 Inputs:  - d1,d2 (double cross dimensions)
          - N     (amount of dipoles (must be an odd number))
 
 Outputs: - xp (x coordinates of the N dipoles relative to the center of the swarm)
          - yp (y coordinates of the N dipoles relative to the center of the swarm)
 %}
function [xp, yp] = d1d2Convert(d1,d2, N)

xp = zeros(1,N);
yp = zeros(1,N); 
    for i = 1:(N-1)/2
        xp(i+1) = d1*cos((i-1)*(2*pi/((N-1)/2)));
        yp(i+1) = d1*sin((i-1)*(2*pi/((N-1)/2)));
    
        xp(i+((N+1)/2)) = d2*cos((i-1)*(2*pi/((N-1)/2))+(pi/((N-1)/2)));
        yp(i+((N+1)/2)) = d2*sin((i-1)*(2*pi/((N-1)/2))+(pi/((N-1)/2)));    
    end

%Note: Notice xp(1)=0 and yp(1)=0. These are the coordinates for 
%the center of the swarm. So later we must also ensure that zp(1)=0.




