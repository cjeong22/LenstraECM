import multiprocessing
import random

MAX_LENGTH = 1 << 62
def power(x, y, p) :
 
    res = 1 # Initialize result 
    x = x % p # Update x if it is more 
              # than or equal to p 
 
    while (y > 0): 
         
        # If y is odd, multiply x with result 
        if (y & 1):
            res = (res * x) % p 
 
        # y must be even now 
        y = y >> 1 # y = y/2 
        x = (x * x) % p 
 
    return res 
 
# Returns true if square root of n under
# modulo p exists. Assumption: p is of the
# form 3*i + 4 where i >= 1 
def squareRoot(n, p): 
 
    if (p % 4 != 3) : 
        print( "Invalid Input" )
        return
 
 
    # Try "+(n^((p + 1)/4))" 
    n = n % p 
    x = power(n, (p + 1) // 4, p) 
    if ((x * x) % p == n): 
        print( "Square root is ", x) 
        return
 
    # Try "-(n ^ ((p + 1)/4))" 
    x = p - x 
    if ((x * x) % p == n): 
        print( "Square root is ", x )
        return
 
    # If none of the above two work, then 
    # square root doesn't exist 
    print( "Square root doesn't exist " )
class InvError(Exception):
  def __init__(self, v):
    self.value = v
# # an implementation of the extended euclidean algorithm
def extended_euclidean(a, b):
  if a == 0:
    return b, 0, 1
  else:
    gcd, x, y = extended_euclidean(b % a, a)
    return gcd, y - (b // a) * x, x

# an implementation of the modular exponentiation algorithm
def modpow(a,n,m):
  def helper(a, n, m):
    res = 1
    count = 0
    while n > 0:
      if (n & 1):
          res = (res * a) % m
      count += 1
      n = n >> 1
      a = (a ** 2) % m
    return res % m
  if n < 0:
    _, a, _ = extended_euclidean(a, m)
    a = a % m
    n = -n
  return helper(a, n, m)

# # this function gets the the inverse of x mod p.
def get_inverse(x : int, p : int):
  def extended_ea(a : int, b: int ):
    if a == 0 :
      return b, 0, 1
    else:
      gcd, x, y = extended_ea(b % a, a)
      return gcd, y - (b//a) * x, x
  gcd, x_inv, _ = extended_ea(x, p)
  if (gcd > 1 and gcd < x):
    raise InvError(gcd) 
  x_inv = x_inv % (p)
  return x_inv

# ec_add is now in the form of P = (x, z)
# P, Q: Points to add 
# A, B: elliptic curve parameters
# p: prime 
# diff P - Q
# def double(P, A, p):
#   x_P = P[0]
#   z_P = P[1]
#   x_res = ((x_P ** 2 - z_P ** 2) ** 2) % p
#   z_res = (4 * x_P * z_P * (x_P ** 2 + z_P ** 2 + A*x_P*z_P)) % p
#   return (x_res, z_res)
# def ec_add(P,Q,A,p,diff):
#   # better caching
#   x_P = P[0]
#   z_P = P[1]
#   x_Q = Q[0]
#   z_Q = Q[1]

#   u = ((x_P + z_P) * (x_Q - z_Q)) % p
#   v = ((x_P - z_P) * (x_Q + z_Q)) % p
#   w = ((u + v) ** 2) % p
#   t = ((u - v) ** 2) % p 
#   x_res = (diff[1] * w) % p 
#   z_res = (diff[0] * t) % p
#   return (x_res, z_res) 
    
# def ec_mult(n,P,A,p):
#   res = P
#   temp = double(P, A, p)
#   while n > 0:
#     if (n & 1):
#       res = ec_add(res, temp, A, p, P)
#       temp = double(P, A, p) # just pass in P for doubling, doesn't matter
#     else:
#       temp = ec_add(temp, res, A, p, P)
#       res = double(res, A, p)
#     n = n >> 1
#  return res
# use the sieve of eratosthenes to keep generating primes until we get the nth one
def sieve_of_eratosthenes(n, *, primes = [2, 3]):
  while len(primes) <= n:
    for i in range(primes[-1] + 2, MAX_LENGTH, 2):
      is_prime = True
      for p in primes:
        if p * p > i:
          break
        if i % p == 0:
          is_prime = False
          break
      if is_prime:
        primes.append(i)
        break
  return primes[n]

def prime_power(idx, bound, *, cache = {}):
  bound2 = 100*bound
  if bound not in cache:
    r = []
    for i in range(MAX_LENGTH):
      p = sieve_of_eratosthenes(i)
      if p >= bound:
        break
      m = p
      while True:
        m2 = m * p # get powers up to a bound 
        if m2 >= bound2:
          break
        m = m2
      r.append(m)
    cache[bound] = r
  return cache[bound][idx] if idx < len(cache[bound]) else None
def ec_add(P,Q,A,p):
    if (Q == 0):
        return P
    if (P == 0):
        return Q
    if (P[0] == Q[0] and P[1] % p == -Q[1] % p):
        return 0
    if (P[0] == Q[0] and P[1] == Q[1]):
        lmda = ((3*modpow(P[0], 2, p) + A) * (get_inverse((2 * P[1]) % p, p))) % p
    else:
        lmda = ((Q[1] - P[1]) * get_inverse((Q[0] - P[0])%p, p)) % p
    x_3 = (modpow(lmda, 2, p) - Q[0] - P[0]) % p
    y_3 = (lmda * (P[0] - x_3) - P[1]) % p
    return (x_3, y_3)
def ec_mult(n,P,A,p):
    temp = 0
    while n > 0:
        if (n & 1):
            temp = ec_add(P, temp, A, p) 
        P = ec_add(P, P, A, p)
        n = n >> 1
    return temp

def ecm_proc(N, bound, shared):
  bound2= bound * 100 # by convention, feel free to change
  try:
    # Suyama's parametrization
    random.seed(random.randrange(1 << 48))
    # sigma = random.randrange(6, N - 1)
    # u = (sigma*sigma - 5) % N
    # v = (4 * sigma) % N
    # x_0 = u**3 % N 
    # z_0 = v**3 % N 
    # temp_inv = get_inverse(4 * (u**3) * v, N)
    # A = (((v - u) ** 3) * (3*u + v) * temp_inv - 2) % N 
    x0, y0, A = [random.randrange(1, N) for i in range(3)]
    # x0 = 2; y0 = 3
    B = (y0 ** 2 - x0 ** 3 - A * x0) % N
    P = (x0, y0)
    # P = (x_0, z_0)
    # stage 1
    for i in range(bound):
      if shared.get('found_factor', False):
        return {'ex': 'finished, joining'}
      k = prime_power(i, bound)
      if k is None:
        break
      P = ec_mult(k, P, A, N)
    # stage 2
    running_total = 1 
    for i in range(bound, bound2):
      if shared.get('found_factor', False):
        return {'ex': 'finished, joining'}
      if k is None:
        break
      k = prime_power(i, bound)
      Q = ec_mult(k, P, A, N)
      running_total = (running_total * Q[1]) % N
      get_inverse(running_total, N)
      P = Q
    return {}
  except InvError as e:
    d = e.value
    if d != N:
      shared['found_factor'] = True
      return {'factors': [d, N // d]}
  except BaseException:
    shared['found_factor'] = True
    return {'ex': 'finished, joining'}
  return {}

def ecm(n):
    processes = multiprocessing.cpu_count()
    length = len(str(n))
    # if length<15:
    #   bound = 2000 
    # elif length<20:
    #   bound = 11000
    # elif length < 25:
    #   bound = 50000
    # else:
    #   bound = 25000000000
    bound = 11000

    with multiprocessing.Manager() as manager, multiprocessing.Pool() as pool:
      dct = manager.dict()
      try:
        proc_retvals = []
        for _ in range(MAX_LENGTH):
          proc_retvals.append(pool.apply_async(ecm_proc, (n, bound, dct)))
          while len(proc_retvals) >= processes * processes:
            temp = []
            for e in proc_retvals:
              if not e.ready():
                temp.append(e)
                continue
              e = e.get()
              if 'factors' in e:
                return e['factors']
            proc_retvals = temp
      except BaseException:
        pass 
      finally:
        dct['found_factor'] = True
        pool.close()
        pool.join()
    return [n]

def main():
  print("System info: running on " + str(multiprocessing.cpu_count()) + " cores")
  N = int(input("Enter an integer to be factored: "))
  fs = ecm(N)
  print(fs)
  print("done!")

if __name__ == '__main__':
  main()