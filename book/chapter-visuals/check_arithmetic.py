"""Check exact worked-example bounds, independently of the drawing runtime."""
from fractions import Fraction as Q
from math import factorial
for stage in range(7):
 n=2**stage
 lower=sum((Q(j*j,n**3) for j in range(n)),Q(0))
 upper=sum((Q((j+1)**2,n**3) for j in range(n)),Q(0))
 assert lower<=Q(1,3)<=upper and upper-lower==Q(1,n)
 h=Q(1,n)
 assert (1-(1-h)**2)/h==2-h and ((1+h)**2-1)/h==2+h
 assert Q(1,2**stage)*2**stage==1
 assert Q(1,2**stage)+Q(1,2**(2*stage+1))==Q(1,2**stage)*(1+Q(1,2**(stage+1)))
for n in range(1,9):
 assert sum((Q(1,2**j) for j in range(n)),Q(0))+Q(1,2**(n-1))==2
 lo,hi=Q(1),Q(2)
 for _ in range(n):
  m=(lo+hi)/2
  if m*m<=2:lo=m
  else:hi=m
 assert lo*lo<=2<=hi*hi and hi-lo==Q(1,2**n)
for n in range(2,9):
 first=Q(4**(n+1),factorial(n+1)**2)
 q=Q(4,(n+2)**2);bound=first/(1-q)
 assert q<1
 # All subsequent terms obey the decreasing ratio. Test the exact finite
 # difference on rational inputs, without using a library Bessel value.
 for z in [Q(j,8) for j in range(33)]:
  prefix=lambda stop:sum(((-1)**j*(z*z/4)**j/factorial(j)**2 for j in range(stop+1)),Q(0))
  assert abs(prefix(30)-prefix(n))<=bound
for n in range(1,11):
 # Integral comparison follows from pointwise rectangle bounds for 1/t^2.
 for k in range(n+1,100):
  assert Q(1,k*(k+1))<=Q(1,k*k)<=Q(1,(k-1)*k)
for k in range(1,8):
 assert Q(k+3,2**(k+2))<Q(k+2,2**(k+1))
print('PASS: exact rectangle gaps, secants, pulse normalization, geometric tails, root brackets, Bessel omitted-term bounds, reciprocal-square comparison and decreasing far-tail budgets')
