from sage.all import *
from reedsolo import RSCodec
from functools import reduce

class KZG():
    
    def __init__(self,
        p=None,
        t=None,
        alpha=None,
        k=16,
        leak=False
        ):
        
        if p is None:
            p = self.safe_random_prime(k)
        elif not p.is_prime():
            raise ValueError("p must be a prime number")
                        
        self.p = p
        self.F_p = GF(p)
        self.g = self.F_p.multiplicative_generator()
        self.alpha = None
        
        if (t is None) or (t >= p):
            self.t = self.__generate_t()
        if alpha is None:
            alpha = self.F_p.random_element()
            self.PP = self.compute_public_parameters(alpha)
        if leak:
            self.alpha = alpha
    
    def __repr__(self):
        
        repr = f"KZG commitment class with {self.F_p} whose generator is {self.g}"
        
        if self.alpha is None:
            return repr + "\nToxic waste has been deleted"
        else:
            return repr + "\nToxic waste has NOT been deleted. Proceed with caution"
        
    @classmethod
    def safe_random_prime(cls, k):
        """Generate a safe random prime.
        Code taken from
        https://ask.sagemath.org/question/44765/randomly-generate-a-safe-prime-of-given-length/?answer=44766#post-id-44766
        """
        while true:
            p = random_prime(2**k - 1, false, 2**(k - 1))
            if ZZ((p - 1)/2).is_prime():
                return p
            
    def polynomial_ring(self, var="x"):
        return PolynomialRing(self.F_p, var).objgen()

    def __polynomial_checks(self, poly):
        if poly.degree() > self.t:
            raise ValueError(f"The polynomial's degree is {poly.degree()}, which is bigger than {self.t}")
        
        if poly.base_ring() != self.F_p:
            raise ValueError("The polynomial must be defined on the same base ring as F_p")
    
    def __generate_t(self):
        t = 0
        while t == 0:
            t = self.F_p.random_element()
        return t
    
    def compute_public_parameters(self, alpha):

        PP = []

        accumulated = 1
        for i in range(self.t + 1):
            PP.append(self.F_p.prod((
                accumulated, self.g
            )))
            accumulated = self.F_p.prod((accumulated, alpha))
        return PP
    
    def make_commitment(self, poly):
        
        self.__polynomial_checks(poly)
        
        # Get the Polynomial coefficients. They are given in ascending order
        poly_coefs = poly.coefficients()

        # Only keep the parameters needed
        pp_used = self.PP[:len(poly_coefs)]  

        return reduce(
            lambda a,b: a + (b[0]*b[1]),
            zip(poly_coefs, pp_used),
            0
        )
    
    def make_opening_triplet(self, i, poly):
        self.__polynomial_checks(poly)

        i_eval = poly(i)
        x = poly.variables()[0]
        
        proof_poly = ((poly - i_eval)/(x - i)).numerator()
        proof_commitment = self.make_commitment(proof_poly)
        return (i, i_eval, proof_commitment)
    
    def verify(self, commitment, opening_triplet):
        
        i, i_eval, proof_commitment = opening_triplet
        
        return (
            self.e(commitment, self.g) == (self.e(proof_commitment, self.PP[1] - i*self.g) + (i_eval*self.e(self.g, self.g)))
        )
    
    def e(self, g1, g2):
        return self.F_p.prod((g1, g2))

def reed_solomon_encode_string(input_string):

    # Initialize the Reed-Solomon encoder/decoder with a specific error correction level
    rs = RSCodec(10)  # You can adjust the error correction level as needed

    # Encode the input string
    encoded_bytes = rs.encode(input_string.encode())

    # Convert the encoded bytes to a list of integers
    return list(encoded_bytes)

def message_as_coords(input_string):
    y = reed_solomon_encode_string(input_string)
    x = range(1, len(y) + 1)
    return list(zip(x, y))

def make_faux_poly(F_p_X, alpha, phi_alpha, i, phi_i):
    xs = [alpha, i]
    ys = [phi_alpha, phi_i]

    F_p = F_p_X.base_ring()

    while (len(xs) != 3):
        x = F_p.random_element()
        if not (x in xs):
            xs.append(x)
            ys.append(F_p.random_element())
    return F_p_X.lagrange_polynomial(zip(xs,ys))