import multiprocessing
import random
import time

# Setting a maximum bound
MAX_LENGTH = 1 << 62
class InversionError(Exception):
  def __init__(self, v):
    self.value = v

# an implementation of the extended euclidean algorithm
# inputs: a, b 
# outputs: gcd(a, b), u, v where au + bv = gcd(a, b)
def extended_euclidean(a : int, b : int):
  if a == 0:
    return b, 0, 1
  else:
    gcd, x, y = extended_euclidean(b % a, a)
    return gcd, y - (b // a) * x, x

# an implementation of the modular exponentiation algorithm
# inputs: a, n, m
# output: a^n % m
def modpow(a : int, n : int, m : int):
  def helper(a : int, n : int, m : int):
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
# inputs: x, p
# output: x^{-1} mod p or InversionError if an inverse does not exist
def get_inverse(x : int, p : int):
  def extended_ea(a : int, b: int):
    if a == 0 :
      return b, 0, 1
    else:
      gcd, x, y = extended_ea(b % a, a)
      return gcd, y - (b//a) * x, x
  gcd, x_inv, _ = extended_ea(x, p)
  if (gcd > 1 and gcd < x): # If our gcd is not equal to 1, then that implies that x is not invertible mod p
    raise InversionError(gcd) 
  x_inv = x_inv % (p)
  return x_inv

# A variant of the sieve of eratosthenes: we generate primes until we reach the nth one 
# Similar to prime_power, we cache the primes as a keyword argument so that we don't
# need to continually recompute primes.
# For example, sieve_of_eratosthenes(1) = 2, sieve_of_eratosthenes(2) = 3, etc. 
def sieve_of_eratosthenes(n : int, *, primes = [2, 3]):
  while len(primes) <= n:
    for i in range(primes[-1] + 2, MAX_LENGTH, 2):
      is_prime = True
      for prime in primes:
        if prime**2 > i:
          break
        if i % prime == 0: # something we've listed is prime is not actually prime.
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
def pow_bound(n : int, bound : int, *, dp = {}): # computes the idxth prime power up to bound
  if bound not in dp:
    pp_list = []
    for i in range(MAX_LENGTH):
      p = sieve_of_eratosthenes(i) # get the ith prime using the sieve of eratosthenes
      if p >= bound: # if our base prime has our bound, we're done and shouldn't return anything
        break
      temp = p
      while 1:
        temp = temp * p # get prime powers up to the bound 
        if temp >= bound: # our prime power has exceeded our bound
          temp = temp // p
          break
      pp_list += [temp] #append this prime power to our dict
    dp[bound] = pp_list
  return dp[bound][n] if n < len(dp[bound]) else None

# ec_add adds points P and Q on the elliptic curve.
# inputs: P, Q (points on elliptic curve), A (paramter of elliptic curve Y^2 = X^3 + AX + B), p (modulus)
# output: P + Q
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
# inputs: n, P (point on elliptic curve), A (paramter of elliptic curve Y^2 = X^3 + AX + B), p (modulus)
# output: nP
def ec_mult(n,P,A,p):
    temp = 0
    while n > 0:
        if (n & 1):
            temp = ec_add(P, temp, A, p) 
        P = ec_add(P, P, A, p)
        n = n >> 1
    return temp

# The bulk of Lenstra ECM.
def ecm_proc(N, bound, dct):
  bound2= bound * 100 #Use B1 to compute B2. B2 = 100*B1 by convention, feel free to change
  try:
    # get a random seed, use that to compute a random point P = (x, y) and a random elliptic curve paramter A
    random.seed(random.randrange(1 << 32))
    x = random.randrange(1, N)
    y = random.randrange(1, N)
    A = random.randrange(1, N)
    P = (x, y)
    # We loop seemingly definitely here (up to a 1 shifted left the maximum amount of bits that signed integers allow us),
    # but notice we have a break occur when we cannot find a prime power that is near B1, so this loop actually does not
    # go on for terribly long.
    for i in range(MAX_LENGTH):
      if dct.get(0) is not None: # this is the case where another process has found a factor. Here we just return nothing
        return {}
      k = pow_bound(i, bound) # obtain a prime power near B1
      if k is None:
        break # break if no more prime powers exist
      P = ec_mult(k, P, A, N) # recompute P
    # By now, we've looped through all prime powers up to B1, so we now shift our attention to B2. This part looks identical
    # to stage 1. Indeed, we don't have projective coordinates to work with here, so we just precompute prime powers
    # for bound2 once again.
    for i in range(MAX_LENGTH):
      if dct.get(0) is not None:
        return {}
      k = pow_bound(i, bound2)
      if k is None:
        break
      P = ec_mult(k, P, A, N)
    return {}
  except InversionError as e:
    d = e.value
    if d != N:
      dct[0] = True
      return {1: [d, N // d]}
    return {}
  except BaseException:
    dct[0] = True
    return {}

# Multiprocessing occurs here, along with setting B1. 
def ecm(n):
  processes = multiprocessing.cpu_count() # get the number of cpus on the machine
  bound = 11000

  with multiprocessing.Manager() as manager, multiprocessing.Pool() as pool:
    dct = manager.dict() # set up a shared memory area so that processes can communicate when one has found a factor
    proc_retvals = [] # get the return values of ecm_proc so that way we 
    try:
      for _ in range(MAX_LENGTH):
        proc_retvals.append(pool.apply_async(ecm_proc, (n, bound, dct)))
        if len(proc_retvals) < processes**2: # we can keep spawning processes here!
          continue
        else:
          while len(proc_retvals) >= processes**2: # we have too many processes, so we must check to see if one of them has found a factor
            temp = []
            for e in proc_retvals:
              if not e.ready(): # if it's not ready to respawn, keep it going
                temp.append(e)
                continue
              e = e.get() # we get the result of apply_async to see if it contains a nontrivial factor, repsented by {1 : (nontrivial factor)}
              if 1 in e:
                return e[1]
            proc_retvals = temp
    except BaseException:
      pass 
    finally:
      dct[0] = True # signal to other processes that we've found a factor
      pool.close() # close the pool
      pool.join() # join all processes
  return [] # we couldn't find any factors :(

# The REPL we use to handle user input
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