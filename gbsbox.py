# -*- coding: utf-8 -*-
r"""
GBSBox - SageMath Module to Analyze S-Boxes using Grobner Bases.

GBSBox is an extension of SBox module that demonstrates a novel approach to analyze
cryptographic properties of S-Boxes using Grobner bases. The primary aim of this work is to
serve as a tool that allows better understanding of algebraic implications from different
cryptographic properties of S-Boxes.

AUTHORS: Rusydi H. Makarim (makarim@cwi.nl)
"""

from six import integer_types

from sage.rings.integer import Integer
from sage.crypto.sbox import SBox
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.ideal import Ideal, FieldIdeal
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.structure.sequence import Sequence


class GBSBox(SBox):
    def __init__(self, *args, **kwargs):
        """
        Construct an instance of GBSBox.

        INPUT:

        - ``S`` - a finite iterable defining the S-box with integer or
          finite field elements

        - ``big_endian`` - controls whether bits shall be ordered in
          big endian order (default: ``True``)

        - ``indexing`` - indexing of variables in the ring (default : 0)
        """
        super().__init__(*args, **kwargs)

        self._linear_ring = None
        self._differential_ring = None
        self._indexing = kwargs.get("indexing", 0)


    def linear_ring(self, order="degrevlex"):
        """
        Return a polynomial ring for linear cryptanalysis.

        INPUT:

        - ``order`` - a monomial order (default : degrevlex)

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox([0, 1, 3, 6, 7, 4, 5, 2], big_endian=False, indexing=1)
            sage: GS.linear_ring()
            Multivariate Polynomial Ring in x1, x2, x3, y1, y2, y3 over Finite Field of size 2
        """
        if self._linear_ring is not None and self._linear_ring.term_order().name() == order:
            return self._linear_ring

        var_names = self.varstrs("x") + self.varstrs("y")
        self._linear_ring = PolynomialRing(GF(2), var_names, order=order)

        return self._linear_ring


    def differential_ring(self, order="degrevlex"):
        """
        Return a polynomial ring for differential cryptanalysis.

        INPUT:

        - ``order`` - a monomial order (default : degrevlex)

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox([0, 1, 3, 6, 7, 4, 5, 2], indexing=1)
            sage: GS.differential_ring()
            Multivariate Polynomial Ring in xl1, xl2, xl3, yl1, yl2, yl3, xr1, xr2, xr3, yr1, yr2, yr3 over Finite Field of size 2
        """
        if self._differential_ring is not None and self._differential_ring.term_order().name() == order:
            return self._differential_ring

        varxl, varyl = self.varstrs("x", "l"), self.varstrs("y", "l")
        varxr, varyr = self.varstrs("x", "r"), self.varstrs("y", "r")
        var_names = varxl + varyl + varxr + varyr
        self._differential_ring = PolynomialRing(GF(2), var_names, order=order)

        return self._differential_ring


    def varformatstr(self, name, postfix):
        """
        Return format string for variable `name` with postfix `postfix`.

        INPUT:

        - ``name`` -- name of variable
        - ``postfix`` -- postfix string

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.varformatstr('x', 'l')
            'xl%d'
        """
        return name + postfix + "%d"


    def varstrs(self, name, postfix=""):
        """
        Return a tuple of variables named `name` with postfix `postfix`.

        INPUT:

        - ``name`` -- name of variable
        - ``postfix`` -- postfix string

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.varstrs('x', 'l')
            ('xl0', 'xl1', 'xl2')
        """
        if name == 'x':
            size = self.input_size()
        elif name == 'y':
            size = self.output_size()
        else:
            raise ValueError("name of variables must either be x or y")

        idx = self._indexing
        return tuple(self.varformatstr(name, postfix) % (i) for i in range(idx, size+idx))


    def vars(self, name, R):
        """
        Return a list of variables for variables named `name` in the ring `R`.

        INPUT:

        - ``name`` - name of variable
        - ``R`` - polynomial ring
        """
        v = [ R(s) for s in R.variable_names() if s.startswith(name) ]

        if self._big_endian is True:
            v.reverse()

        return v


    def linear_vars(self, name):
        """
        Return a list of variables for variables named `name` for linear cryptanalysis.

        INPUT:

        - ``name`` - name of variables

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2, big_endian=False)
            sage: GS.linear_vars('x')
            [x0, x1, x2]
            sage: GS.linear_vars('y')
            [y0, y1, y2]
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2, big_endian=True)
            sage: GS.linear_vars('x')
            [x2, x1, x0]
            sage: GS.linear_vars('y')
            [y2, y1, y0]
        """
        return self.vars(name, self.linear_ring())


    def differential_vars(self, name):
        """
        Return a list of variables for variables named `name` for differential cryptanalysis.

        INPUT:

        - ``name`` - name of variables

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2, big_endian=False)
            sage: GS.differential_vars('xl')
            [xl0, xl1, xl2]
            sage: GS.differential_vars('y')
            [yl0, yl1, yl2, yr0, yr1, yr2]
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2, big_endian=True)
            sage: GS.differential_vars('xl')
            [xl2, xl1, xl0]
            sage: GS.differential_vars('y')
            [yr2, yr1, yr0, yl2, yl1, yl0]
        """
        return self.vars(name, self.differential_ring())


    def twoinput_polynomials(self):
        """
        Return a system of equations that represent two inputs to this S-Box.

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: F = GS.twoinput_polynomials()
            sage: for f in F: print(f)
            xl0*xl2 + xl1 + xl2 + yl1
            xl1*xl2 + xl0 + xl1 + xl2 + yl0
            xl2*yl1 + xl0 + xl2 + yl0 + yl1
            xl2*yl0 + xl1 + yl1
            xl0*xl1 + xl2 + yl2
            xl1*yl2 + xl0 + xl1 + yl0 + yl2
            xl1*yl1 + xl2*yl2 + xl0 + yl0
            xl1*yl0 + xl1 + xl2 + yl2
            xl0*yl2 + xl1 + yl1 + yl2
            xl0*yl1 + xl2 + yl2
            xl0*yl0 + xl2*yl2 + xl0 + xl1 + xl2 + yl1 + yl2
            yl1*yl2 + xl0 + yl0 + yl1 + yl2
            yl0*yl2 + xl1 + yl1
            yl0*yl1 + xl2 + yl1 + yl2
            xr0*xr2 + xr1 + xr2 + yr1
            xr1*xr2 + xr0 + xr1 + xr2 + yr0
            xr2*yr1 + xr0 + xr2 + yr0 + yr1
            xr2*yr0 + xr1 + yr1
            xr0*xr1 + xr2 + yr2
            xr1*yr2 + xr0 + xr1 + yr0 + yr2
            xr1*yr1 + xr2*yr2 + xr0 + yr0
            xr1*yr0 + xr1 + xr2 + yr2
            xr0*yr2 + xr1 + yr1 + yr2
            xr0*yr1 + xr2 + yr2
            xr0*yr0 + xr2*yr2 + xr0 + xr1 + xr2 + yr1 + yr2
            yr1*yr2 + xr0 + yr0 + yr1 + yr2
            yr0*yr2 + xr1 + yr1
            yr0*yr1 + xr2 + yr1 + yr2
        """

        xl, yl = self.differential_vars('xl'), self.differential_vars('yl')
        xr, yr = self.differential_vars('xr'), self.differential_vars('yr')

        F = []
        Fl, Fr = [], []
        deg = 2
        while not Fl or not Fr:
            Fl = self.polynomials(X=xl, Y=yl, degree=deg)
            Fr = self.polynomials(X=xr, Y=yr, degree=deg)
            deg += 1
        F += Fl + Fr

        return Sequence(F)


    def linear_ideal(self, a, b, order="degrevlex"):
        """
        Return the linear ideal with input mask `a` and output mask `b`.

        INPUT:

        - ``a`` -- input mask
        - ``b`` -- output mask
        - ``order`` - monomial ordering (default : degrevlex)

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 3, 5, 8, 6, 10, 15, 4, 14, 13, 9, 2, 1, 7, 12, 11)
            sage: I = GS.linear_ideal(3, 1)
            sage: (I.vector_space_dimension() - 8) == 4
            True
        """
        m, n = self.input_size(), self.output_size()
        x, y = self.linear_vars('x'), self.linear_vars('y')

        if isinstance(a, integer_types + (Integer,)):
            a = self.to_bits(a, m)
        if isinstance(b, integer_types + (Integer,)):
            b = self.to_bits(b, n)

        F = []
        deg = 2
        while not F:
            F = self.polynomials(X=x, Y=y, degree=deg)
            deg += 1

        F += [ sum(a[i]*x[i] for i in range(m)) + sum(b[j]*y[j] for j in range(n)) ]

        R = self.linear_ring(order)
        I = Ideal(R, F) + FieldIdeal(R)

        return I


    def autocorrelation_ideal(self, a, b, order="degrevlex"):
        """
        Return the autocorrelation ideal with input difference `a` and output mask `b`.

        INPUT:

        - ``a`` - input difference
        - ``b`` - output mask
        - ``order`` - monomial ordering (default : degrevlex)

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 3, 5, 8, 6, 10, 15, 4, 14, 13, 9, 2, 1, 7, 12, 11)
            sage: I = GS.autocorrelation_ideal(3, 1)
            sage: act = GS.autocorrelation_table()
            sage: (16 - 2*I.vector_space_dimension()) == act[3, 1]
            True
        """
        F = self.twoinput_polynomials()

        xl, xr = self.differential_vars("xl"), self.differential_vars("xr")
        yl, yr = self.differential_vars("yl"), self.differential_vars("yr")
        m, n = self.input_size(), self.output_size()
        if isinstance(a, integer_types + (Integer,)):
            a = self.to_bits(a, m)
        if isinstance(b, integer_types + (Integer,)):
            b = self.to_bits(b, n)
        F += [ xl[i] + xr[i] + a[i] for i in range(m) ]
        F += [ sum([ b[j]*(yl[j] + yr[j]) for j in range(n) ]) + 1 ]

        R = self.differential_ring(order)
        I = Ideal(R, F) + FieldIdeal(R)

        return I


    def differential_ideal(self, a, b=None, order="degrevlex"):
        """
        Return a multivariate ideal for differential cryptanalysis.

        INPUT:

        - ``a`` -- input difference
        - ``b`` -- output difference (optional)
        - ``order`` -- monomial ordering (default : degrevlex)

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 3, 5, 8, 6, 10, 15, 4, 14, 13, 9, 2, 1, 7, 12, 11)
            sage: F = GS.differential_ideal(4, order="lex")
            sage: G = F.groebner_basis()
            sage: for g in G: print(g)
            xl0 + yr0*yr1*yr3 + yr0*yr2*yr3 + yr0*yr2 + yr0*yr3 + yr1*yr3 + yr1 + yr2 + yr3
            xl1 + yr0*yr1*yr2 + yr0*yr1 + yr0*yr2*yr3 + yr1 + yr2*yr3 + yr2 + yr3
            xl2 + yr0*yr1*yr3 + yr0*yr1 + yr0*yr2*yr3 + yr0*yr3 + yr0 + yr1*yr3 + yr2 + 1
            xl3 + yr0*yr1*yr2 + yr0*yr2 + yr0 + yr1*yr2*yr3 + yr1*yr2 + yr1*yr3 + yr1 + yr2*yr3
            yl0 + yr0*yr1*yr2 + yr0*yr1 + yr0*yr2*yr3 + yr0*yr2 + yr1*yr2 + yr1 + yr2*yr3
            yl1 + yr0*yr1*yr2 + yr0*yr2 + yr1*yr2*yr3 + yr1*yr3 + yr2*yr3 + yr2 + yr3 + 1
            yl2 + yr0*yr2 + yr1*yr2 + yr1 + yr2 + 1
            yl3 + yr0*yr1 + yr0*yr2*yr3 + yr0*yr2 + yr0 + yr1*yr2*yr3 + yr1*yr3 + yr1 + yr2
            xr0 + yr0*yr1*yr3 + yr0*yr2*yr3 + yr0*yr2 + yr0*yr3 + yr1*yr3 + yr1 + yr2 + yr3
            xr1 + yr0*yr1*yr2 + yr0*yr1 + yr0*yr2*yr3 + yr1 + yr2*yr3 + yr2 + yr3
            xr2 + yr0*yr1*yr3 + yr0*yr1 + yr0*yr2*yr3 + yr0*yr3 + yr0 + yr1*yr3 + yr2
            xr3 + yr0*yr1*yr2 + yr0*yr2 + yr0 + yr1*yr2*yr3 + yr1*yr2 + yr1*yr3 + yr1 + yr2*yr3
            yr0^2 + yr0
            yr1^2 + yr1
            yr2^2 + yr2
            yr3^2 + yr3
        """
        F = self.twoinput_polynomials()

        xl, xr = self.differential_vars("xl"), self.differential_vars("xr")
        m = self.input_size()
        if isinstance(a, integer_types + (Integer,)):
            a = self.to_bits(a, m)
        F += [ xl[i] + xr[i] + a[i] for i in range(m) ]

        if b is not None:
            yl, yr = self.differential_vars("yl"), self.differential_vars("yr")
            n = self.output_size()
            if isinstance(b, integer_types + (Integer,)):
                b = self.to_bits(b, n)
            F += [ yl[i] + yr[i] + b[i] for i in range(n) ]

        R = self.differential_ring(order=order)
        I = Ideal(R, F) + FieldIdeal(R)

        return I


    def gb_linear_structures(self):
        r"""
        Return a tuple of (b, a, c) s.t. `a` is a `c`-linear structure of the
        component function `b \cdot S`.

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: gb_ls = GS.gb_linear_structures()
            sage: ls = GS.linear_structures()
            sage: all( s in ls for s in gb_ls )
            True
            sage: len(gb_ls) == len(ls)
            True
        """
        ret = []
        F = self.twoinput_polynomials()
        B = self.differential_ring()

        m, n = self.input_size(), self.output_size()
        xl, yl = self.differential_vars("xl"), self.differential_vars("yl")
        xr, yr = self.differential_vars("xr"), self.differential_vars("yr")

        for a in range(1, 1 << m):
            va = self.to_bits(a, m)
            Fa = Sequence(F + [ xl[i] + xr[i] + va[i] for i in range(m) ], B)
            Ga = Fa.groebner_basis()
            I = Ga.ideal()
            for b in range(1, 1 << n):
                vb = self.to_bits(b, n)
                f = B(sum(vb[i] * yl[i] + vb[i] * yr[i] for i in range(n)))
                c = I.reduce(f)
                if c == 0 or c == 1:
                    ret.append( (b, a, c) )

        return ret


    def gb_linear_bias(self, a, b):
        """
        Return the linear bias of this S-Box.

        INPUT:

        - ``a`` - input mask
        - ``b`` - output mask

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: lat = GS.linear_approximation_table()
            sage: lat[1, 3] == GS.gb_linear_bias(1, 3)
            True
        """
        I = self.linear_ideal(a, b)
        return I.vector_space_dimension() - (1 << (self.input_size() - 1))


    def gb_autocorrelation(self, a, b):
        """
        Return the autocorrelation of this S-Box.

        INPUT:

        - ``a`` - input difference
        - ``b`` - output mask

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: act = GS.autocorrelation_table()
            sage: act[1, 3] == GS.gb_autocorrelation(1, 3)
            True
        """
        I = self.autocorrelation_ideal(a, b)
        return (1 << self.input_size()) - (2 * I.vector_space_dimension())


    def gb_differential_probability(self, a, b, get_numerator=False):
        """
        Return the differential probability of this S-Box.

        INPUT:

        - ``a`` - input difference
        - ``b`` - output difference
        - ``get_numerator`` - return only the numerator (default : False)

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: ddt = GS.difference_distribution_table()
            sage: ddt[1, 3] == GS.gb_differential_probability(1, 3, get_numerator=True)
            True
        """
        I = self.differential_ideal(a, b)
        num = I.vector_space_dimension()

        ret = 0
        if get_numerator:
            ret = num
        else:
            ret = num / (1 << self.input_size())

        return ret


    def gb_linear_approximation_table(self):
        """
        Return the linear approximation table using Grobner bases algorithm.

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: lat = GS.linear_approximation_table()
            sage: gb_lat = GS.gb_linear_approximation_table()
            sage: lat == gb_lat
            True
        """
        m, n = self.input_size(), self.output_size()
        nrows, ncols = 1 << m, 1 << n
        gblb = self.gb_linear_bias
        entries = [ gblb(a, b) for a in range(nrows) for b in range(ncols)]
        return Matrix(ZZ, entries, nrows=nrows, ncols=ncols)


    def gb_autocorrelation_table(self):
        """
        Return the autocorrelation table using Grobner bases algorithm.

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: act = GS.autocorrelation_table()
            sage: gb_act = GS.gb_autocorrelation_table()
            sage: act == gb_act
            True
        """
        m, n = self.input_size(), self.output_size()
        nrows, ncols = 1 << m, 1 << n
        gbac = self.gb_autocorrelation
        entries = [ gbac(a, b) for a in range(nrows) for b in range(ncols)]
        return Matrix(ZZ, entries, nrows=nrows, ncols=ncols)


    def gb_difference_distribution_table(self):
        """
        Return the difference distribution table using Grobner bases algorithm.

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: ddt = GS.difference_distribution_table()
            sage: gb_ddt = GS.gb_difference_distribution_table()
            sage: ddt == gb_ddt
            True
        """
        m, n = self.input_size(), self.output_size()
        nrows, ncols = 1 << m, 1 << n
        gbdp = self.gb_differential_probability
        entries = [ gbdp(a, b, get_numerator=True) for a in range(nrows) for b in range(ncols)]
        return Matrix(ZZ, entries, nrows=nrows, ncols=ncols)


    def gb_nonlinearity(self):
        """
        Return the nonlinearity of this S-Box using Grobner bases algorithm.

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.gb_nonlinearity() == GS.nonlinearity()
            True
        """
        m, n = self.input_size(), self.output_size()
        gblb = self.gb_linear_bias

        nl = (1 << (m-1)) - max( abs(gblb(a, b)) for a in range(1 << m) for b in range(1, 1 << n) )

        return nl


    def gb_differential_uniformity(self):
        """
        Return the differential uniformity of this S-Box using Grobner bases algorithm.

        EXAMPLES::

            sage: load("gbsbox.py")
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.gb_differential_uniformity()
            2
        """
        m, n = self.input_size(), self.output_size()
        gbdp = self.gb_differential_probability

        d = max( gbdp(a, b, get_numerator=True) for a in range(1, 1<<m) for b in range(1<<n))

        return d
