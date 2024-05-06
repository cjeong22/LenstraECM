import multiprocessing
import random
import time

# Setting a maximum bound
MAX_LENGTH = 1 << 62
class InversionError(Exception):
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

# an implementation of modular inversion
def get_inverse(x : int, p : int):
  def extended_ea(a : int, b: int ):
    if a == 0 :
      return b, 0, 1
    else:
      gcd, x, y = extended_ea(b % a, a)
      return gcd, y - (b//a) * x, x
  gcd, x_inv, _ = extended_ea(x, p)
  if (gcd > 1 and gcd < x):
    raise InversionError(gcd) 
  x_inv = x_inv % (p)
  return x_inv

# A variant of the sieve of eratosthenes: we generate primes until we reach the nth one 
# Similar to prime_power, we cache the primes as a keyword argument so that we don't
# need to continually recompute primes.
# For example, sieve_of_eratosthenes(1) = 2, sieve_of_eratosthenes(2) = 3, etc. 
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

# prime_power computes the maximal power of the nth prime that is less than bound.
# For example, prime_power(0, 10) => 8, prime_power(0, 17) => 16, prime_power(1, 200) -> 125
# This is the how we precompute primes for stage 2! All calls to prime_power manipulate the 
# same dp dictionary, so we do not have to reperform any expensive computations. 
def prime_power(n, bound, *, dp = {}): # computes the idxth prime power up to bound
  if bound not in dp:
    r = []
    for i in range(MAX_LENGTH):
      p = sieve_of_eratosthenes(i) # get the ith prime using the sieve of eratosthenes
      if p >= bound: # if we;ve exceeded our bound, we're done
        break
      m = p
      while True:
        m2 = m * p # get prime powers up to the bound 
        if m2 >= bound:
          break
        m = m2
      r.append(m) #append this prime power to our dict
    dp[bound] = r
  return dp[bound][n] if n < len(dp[bound]) else None

# ec_add adds points P and Q on the elliptic curve.
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

# ec_mult returns nP, where P is a point on the elliptic curve
def ec_mult(n,P,A,p):
    temp = 0
    while n > 0:
        if (n & 1):
            temp = ec_add(P, temp, A, p) 
        P = ec_add(P, P, A, p)
        n = n >> 1
    return temp

# The bulk of Lenstra ECM.
def ecm_proc(N, bound, shared):
  bound2= bound * 100 # by convention, feel free to change
  try:
    random.seed(random.randrange(1 << 48))
    x0, y0, A = [random.randrange(1, N) for _ in range(3)]
    P = (x0, y0)
    for i in range(MAX_LENGTH):
      if shared.get(0, False):
        return {}
      k = prime_power(i, bound)
      if k is None:
        break
      P = ec_mult(k, P, A, N)
    # stage 2
    for i in range(MAX_LENGTH):
      if shared.get(0, False):
        return {}
      if k is None:
        break
      k = prime_power(i, bound2)
      P = ec_mult(k, P, A, N)
    return {}
  except InversionError as e:
    d = e.value
    if d != N:
      shared[0] = True
      return {1: [d, N // d]}
    return {}
  except BaseException:
    shared[0] = True
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
    # elif length < 30:
    #   bound = 250000
    # elif length < 35:
    #   bound = 1000000
    # else:
    #   bound = 25000000000
    bound = 11000

    with multiprocessing.Manager() as manager, multiprocessing.Pool() as pool:
      dct = manager.dict()
      try:
        proc_retvals = []
        for _ in range(MAX_LENGTH):
          proc_retvals.append(pool.apply_async(ecm_proc, (n, bound, dct)))
          if len(proc_retvals) < processes * 9:
            continue
          while len(proc_retvals) >= processes * 6:
            temp = []
            for e in proc_retvals:
              if not e.ready():
                temp.append(e)
                continue
              e = e.get()
              if 1 in e:
                return e[1]
            proc_retvals = temp
      except BaseException:
        pass 
      finally:
        dct[0] = True
        pool.close()
        pool.join()
    return [n]

def main():
  print("System info: running on " + str(multiprocessing.cpu_count()) + " cores")
  print("Type \"quit\" to quit")
  N = 0
  while True:
    try:
      _input = input("Enter an integer to be factored: ")
      if (_input == 'quit'):
        print("Quitting")
        return
      N = int(_input)
      break
    except ValueError:
      print("Please input an integer")
  start = time.time()
  fs = ecm(N)
  end = time.time()
  print(fs)
  print("Time taken: " + str(end-start))
  print("done!")

if __name__ == '__main__':
  main()