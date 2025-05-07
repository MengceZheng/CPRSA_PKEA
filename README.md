# A Novel Partial Key Exposure Attack on Common Prime RSA

## Introduction

This is a Python implementation of lattice-based attack proposed in **A Novel Partial Key Exposure Attack on Common Prime RSA**[^CPRSAPKEA].

## Requirements

- [**SageMath**](https://www.sagemath.org/) 9.5 with Python 3.10

You can check your SageMath Python version using the following command:

```commandline
$ sage -python --version
Python 3.10.12
```

Note: If your SageMath Python version is older than 3.9.0, some features in given scripts might not work.

## Usage

The standard way to run the attack with the specific parameters $\ell$, $\gamma$, $\delta$, $\delta_{MSB}$, $\delta_{LSB}$, and $m$ requires passing them as command line arguments `sage -python attack.py <modulus_bit_length> <gamma> <delta> <delta_MSB> <delta_LSB> <m>`. For instance, to run the attack with $\ell=256$, $\gamma=0.25$, $\delta=0.21$, $\delta_{MSB}=0.08$, $\delta_{LSB}=0.08$ and $m=2$, please run `sage -python attack.py 256 0.25 0.21 0.08 0.08 2`:

```commandline
CPRSA_PKEA$ sage -python attack.py 256 0.25 0.21 0.08 0.08 2
The known parameters:
N = 76876466992225920318655704826542477732956384364138188516083215741791052291075
e = 1101013615240191616460402738709355824552439800233065022863
MSB = 906374
LSB = 977695
Found primes:
p = 257368528655002736035880964198176665695
q = 298701894104843162567582663120253822685
The attack costs 0.45 seconds...
```

## Notes

All the details of the numerical attack experiments are recorded in the `attack.log` file.

[^CPRSAPKEA]: Zheng M., Nitaj A., "A Novel Partial Key Exposure Attack on Common Prime RSA"
