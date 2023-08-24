# The ElGamal Cryptosystem

The ElGamal Cryptosystem may be defined over the group $\left(\mathbb{Z}_{p}^{*}, \cdot\right)$, where $\mathbb{Z}_{p}^{*}$ is the set of all integers in the interval $[1,\cdots,p-1]$ and $p$ is prime. But this cryptosystem may also be defined over the group $\left(\mathbb{F}_{p^{n}}^{*}, \cdot\right)$, where $\mathbb{F}_{p^{n}}^{*}=\mathbb{Z}_{p}^{*}[w]/f(w)$ without the polynomial equal to zero, $p$ is prime, $n$ is an positive integer and $f(w)\in\mathbb{Z}_{p}$ is a polynomial of degree $n$. $\mathbb{Z}_{p}^{*}[w]$ is the set of all polynomials under inderteminate $w$ with coeficients in the set $\mathbb{Z}_{p}$ without the polynomial equal to zero. The set $\mathbb{Z}_{p}^{*}[w]/f(w)$ is the set of all polynomial of degree less than $n$ and that are reduced by the polynomial $f(w)$ without the polynomial equal to zero.

The ElGamal Cryptosystem is defined over $\left(\mathbb{F}_{p^{n}}^{*}, \cdot\right)$ as follows:
- $\alpha\in\mathbb{F}_{p^{n}}^{*}$ is a primitive element. $\mathcal{P}=\mathbb{F}_{p^{n}}^{*}$ is the set of plaintexts. $\mathcal{C}=\mathbb{F}_{p^{n}}^{*}\times\mathbb{F}_{p^{n}}^{*}$ is the set of ciphertexts.
- Define $\mathcal{K}=\{(p,n,\alpha,\beta,a):\beta=\alpha^{a} \mod f(w)\}$, where $p$, $n$, $\alpha$ and $\beta$ are the public key and $a$ is the private key.
- For a random integer $k\in\mathbb{Z}_{p^{n}-1}$, define $$e_{K}(x, k)=(y_{1},y_{2})$$where $$y_{1}=\alpha^{k}\mod f(w)$$ and $$y_{2}=x\beta^{k}\mod f(w)$$
- For decryption we have: $$d_{K}(y_{1},y_{2})=y_{2}(y_{1}^{a})^{-1}\mod f(w)$$

Suppose we have the ElGamal Cryptosystem defined over $\left(\mathbb{F}_{3^{3}}, \cdot\right)$, where $f(w)=w^{3}+2x^{2}+1$ is irreducible over $\mathbb{Z}_{3}[w]$, in other words, $f(w)$ cannot be factored in other two polynomials over this field. And we have that $\alpha=w$ a primitive element, $a=11$ and $\beta=w+2=\alpha^{a}\mod f(w)=w^{11}\mod f(w)$.

Suppose we have the following correspondence for every character of the alphabet with the polynomial of $\mathbb{F}_{3^{3}}^{*}$:
\begin{equation}
\begin{array}{rclrclrcl}
A & \leftrightarrow & 1 & B & \leftrightarrow & 2 & C & \leftrightarrow & w\\
D & \leftrightarrow & w+1 & E & \leftrightarrow & w+2 & F & \leftrightarrow & 2w\\
G & \leftrightarrow & 2w+1 & H & \leftrightarrow & 2w+2 & I & \leftrightarrow & w^{2}\\
J & \leftrightarrow & w^{2}+1 & K & \leftrightarrow & w^{2}+2 & L & \leftrightarrow & w^{2}+w\\
M & \leftrightarrow & w^{2}+w+1 & N & \leftrightarrow & w^{2}+w+2 & O & \leftrightarrow & w^{2}+2w\\
P & \leftrightarrow & w^{2}+2w+1 & Q & \leftrightarrow & w^{2}+2w+2 & R & \leftrightarrow & 2w^{2}\\
S & \leftrightarrow & 2w^{2}+1 & T & \leftrightarrow & 2w^{2}+2 & U & \leftrightarrow & 2w^{2}+w\\
V & \leftrightarrow & 2w^{2}+w+1 & X & \leftrightarrow & 2w^{2}+w+2 & W & \leftrightarrow & 2w^{2}+2w\\
Y & \leftrightarrow & 2w^{2}+2w+1 & Z & \leftrightarrow & 2w^{2}+2w+2 &  &  & \\
\end{array}
\end{equation}

And we want to decrypt the following ciphertexts:
$$(K, H)\ (P, X)\ (N, K)\ (H, R)\ (T, F)\ (V, Y)\ (E, H)\ (F, A)\ (T, W)\ (J, D)\ (U, J)$$
So let's do a code for solve this for us.

First we import some libraries that will help us with data treatment.


```python
import numpy as np
```

## Arithmetics with polynomials and fields
Now we write some functions for arithmetics with polynomials and other helper functions


```python
'''
This function makes the product of two polynomials reduced modulo f(w)=w^3+2*w^2+1
'''
def mult_Fq(poly1, poly2):
    # Multiplis the two polynomials
    poly = list(np.polymul(poly1, poly2))
    
    # Make sure that there is 5 entries in the array
    while len(poly) < 5:
        poly.insert(0, 0)
        
    # Reduce the polynomial by the polynomial f(w) using division of polynomials
    poly = [
        poly[0] + poly[1] + poly[2],
        poly[3] + 2 * poly[0], 
        poly[4] + 2 * poly[0] + 2 * poly[1]
    ]
    
    # Make sure all the coeficients are reduced modulo 3
    poly = [*map(lambda t: t % 3, poly)]
    return poly

'''
This function makes the exponetiation of a polynomial reduced modulo f(w)=w^3+2*w^2+1
'''
def exp_Fq(poly1, a):
    # Returns the polynomial f(w)=1 if the exponent is zero
    if a == 0:
        return [0, 0, 1]
    
    # Uses the multiplication algorithm for the exponetiation. 
    # This could be enhanced using a form the square and multiply algorithm
    poly = poly1.copy()
    for i in range(a - 1):
        poly = mult_Fq(poly, poly1)
    return poly

'''
This function converts some integer to base 3 with the output digits in a array
'''
def int2base3(n):
    poly = []
    while n != 0:
        poly.insert(0, n % 3)
        n = n // 3
        
    # Make sure that the array has length 3
    while len(poly) != 3:
        poly.insert(0, 0)
    return poly


'''
This function converts an input array on base 3 to integer.
Is an invert of the previous function.
'''
def base32int(poly):
    n = poly[0]
    for i in range(1,len(poly)):
        n *= 3
        n += poly[i]
    return n
```

## Decryption code
We write the code that makes the decryption of a ciphertext in this specified problem of the ElGamal Cryptosystem


```python
'''
Decrypts the ciphertext y1 and y2 using information about the ElGamal cryptosystem.
'''
def decrypt(y1, y2, a, alpha, alphabet):
    # Find the value of y1^a reduced f(w)
    y1_a = exp_Fq(y1, a)
    
    # Find the invert polynomial g(w) such that g(w) * y1^a mod f(w) = 1.
    # This is made by the dictionary of the alphabet using the primitive element 
    # to generate all the polynomials of the field.
    character = chr(base32int(y1_a) + ord('A') - 1) # Gets which character y1^a corresponds to.
    i = alphabet[character] # Gets what exponent i such that alpha^i = y1^a
    log_alpha_y1_a_inv = 26 - i # So, the exponent of g(w) will be 26 - i
    if log_alpha_y1_a_inv == 0: # The invert of 1 is 1
        log_alpha_y1_a_inv = 1
    gw = exp_Fq(alpha, log_alpha_y1_a_inv) # Gets g(w)
    
    # Return the decryption multiplying g(w) by the y2
    return chr(base32int(mult_Fq(y2, gw)) + ord('A') - 1)
```

## Some visualization before solving it
The code below shows the correspondences of the characters to the polynomials.


```python
alphabet = {}
for i in range(1,27):
    alphabet[chr(i + ord('A') - 1)] = int2base3(i)
    
alphabet
```




    {'A': [0, 0, 1],
     'B': [0, 0, 2],
     'C': [0, 1, 0],
     'D': [0, 1, 1],
     'E': [0, 1, 2],
     'F': [0, 2, 0],
     'G': [0, 2, 1],
     'H': [0, 2, 2],
     'I': [1, 0, 0],
     'J': [1, 0, 1],
     'K': [1, 0, 2],
     'L': [1, 1, 0],
     'M': [1, 1, 1],
     'N': [1, 1, 2],
     'O': [1, 2, 0],
     'P': [1, 2, 1],
     'Q': [1, 2, 2],
     'R': [2, 0, 0],
     'S': [2, 0, 1],
     'T': [2, 0, 2],
     'U': [2, 1, 0],
     'V': [2, 1, 1],
     'W': [2, 1, 2],
     'X': [2, 2, 0],
     'Y': [2, 2, 1],
     'Z': [2, 2, 2]}



We know that $$\alpha=w,$$ $$\beta=w+2$$ and $$a=11$$


```python
alpha = [0, 1, 0]
beta = [0, 1, 2]
a = 11
```

In the code below, we make an alphabet dictionary using that $\alpha$ is a primitive element, in other words, it is a generator of the field. That is $$p(w)=\alpha^{i}\mod f(w), \text{ for some } i\geq 0$$ for all $p(w)\in\mathbb{F}_{p^{n}}^{*}$.

The alphabet contains the exponents $i$ such that each polynomial (character) can be generated. For example, you see that 'X' = 6. So we know that $$\text{'X'}=[2, 2, 0] = 2w^{2}+2w = w^{6}\mod f(w)$$ where $f(w)=w^{3}+2w^{2}+1$.


```python
alphabet_exponents = {}
for i in range(26):
    poly = exp_Fq(alpha, i)
    character = chr(base32int(poly) + ord('A') - 1)
    alphabet_exponents[character] = i
    
alphabet_exponents
```




    {'A': 0,
     'C': 1,
     'I': 2,
     'K': 3,
     'Q': 4,
     'H': 5,
     'X': 6,
     'J': 7,
     'N': 8,
     'Z': 9,
     'P': 10,
     'E': 11,
     'O': 12,
     'B': 13,
     'F': 14,
     'R': 15,
     'S': 16,
     'V': 17,
     'D': 18,
     'L': 19,
     'T': 20,
     'Y': 21,
     'M': 22,
     'W': 23,
     'G': 24,
     'U': 25}



## Decryption of the ciphertexts
Now, we decrypt the cipehrtexts


```python
ciphertext = [
    ('K', 'H'),
    ('P', 'X'),
    ('N', 'K'),
    ('H', 'R'),
    ('T', 'F'),
    ('V', 'Y'),
    ('E', 'H'),
    ('F', 'A'),
    ('T', 'W'),
    ('J', 'D'),
    ('U', 'J')
]

# Each ciphertext is dercypted separately
plaintext = ''
for y1, y2 in ciphertext:
    plaintext += decrypt(
        int2base3(ord(y1) - ord('A') + 1),
        int2base3(ord(y2) - ord('A') + 1),
        a,
        alpha,
        alphabet_exponents
    )
```

And we get that the plaintext is:


```python
print('The plaintext is:', plaintext)
```

    The plaintext is: GALOISFIELD
    

## Reference
I took this example from the book *Criptography: Theory and Practice* from Stinson and Paterson, fourth edition, chapter 7: *Public-key Cryptography and Discrete Logarithms*.
