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
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.ideal import Ideal, FieldIdeal
from sage.rings.integer_ring import ZZ
from sage.rings.polynomial.pbori import BooleanPolynomialRing
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
        """
        super(GBSBox, self).__init__(*args, **kwargs)
        self._algdiff_ring = None

    def algebraic_differential_ring(self, order="degrevlex", use_polybori=False):
        """
        Return a polynomial ring for algebraic-differential analysis.

        INPUT:

        - ``order`` - a monomial order (default : degrevlex)
        - ``use_polybori`` - use Boolean polynomial ring (default : False)

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.algebraic_differential_ring()
            Multivariate Polynomial Ring in xl0, xl1, xl2, yl0, yl1, yl2, xr0, xr1, xr2, yr0, yr1, yr2 over Finite Field of size 2
            sage: GS.algebraic_differential_ring(order="deglex", use_polybori=True)
            Boolean PolynomialRing in xl0, xl1, xl2, yl0, yl1, yl2, xr0, xr1, xr2, yr0, yr1, yr2
        """

        if self._algdiff_ring is not None and use_polybori is False:
            return self._algdiff_ring

        varxl, varyl = self.varstrs("x", "l"), self.varstrs("y", "l")
        varxr, varyr = self.varstrs("x", "r"), self.varstrs("y", "r")
        var_names = varxl + varyl + varxr + varyr

        if use_polybori:
            # The Boolean polynomial ring is needed to convert the polynomials into
            # Boolean polynomials for faster Grobner bases computation.
            R = BooleanPolynomialRing(len(var_names), var_names, order=order)
        else:
            # Computing algebraic representation of an SBox must be done using
            # polynomial ring of Singular because calling self.polynomials(X, Y) is slow
            # when X, Y are defined over Boolean polynomial ring
            R = PolynomialRing(GF(2), var_names, order=order)
            self._algdiff_ring = R

        return R


    def varformatstr(self, name, postfix):
        """
        Return format string for variable `name` with postfix `postfix`.

        INPUT:

        - ``name`` - name of variable
        - ``postfix`` - postfix string

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.varformatstr('x', 'l')
            'xl%d'
        """
        return name + postfix + "%d"


    def varstrs(self, name, postfix):
        """
        Return a tuple of variables named `name` with postfix `postfix`.

        INPUT:

        - ``name`` - name of variable
        - ``postfix`` - postfix string

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.varstrs('x', 'l')
            ('xl0', 'xl1', 'xl2')
        """
        if name == 'x':
            size = self.input_size()
        elif name == 'y':
            size = self.output_size()

        return tuple(self.varformatstr(name, postfix) % (i) for i in range(size))


    def vars(self, name):
        """
        Return a tuple of variables for variables named `name`.

        INPUT:

        - ``name`` -- name of variable

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2, big_endian=False)
            sage: GS.vars('xl')
            [xl0, xl1, xl2]
            sage: GS.vars('y')
            [yl0, yl1, yl2, yr0, yr1, yr2]
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2, big_endian=True)
            sage: GS.vars('xl')
            [xl2, xl1, xl0]
            sage: GS.vars('y')
            [yr2, yr1, yr0, yl2, yl1, yl0]
        """
        R = self.algebraic_differential_ring()
        v = [R(s) for s in R.variable_names() if s.startswith(name)]

        if self._big_endian is True:
            v.reverse()

        return v


    def twoinput_polynomials(self):
        """
        Return a system of equations that represent two inputs to this S-Box.

        EXAMPLES::

            sage: from gbsbox import GBSBox
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

        xl, yl = self.vars('xl'), self.vars('yl')
        xr, yr = self.vars('xr'), self.vars('yr')

        F = []
        Fl, Fr = [], []
        deg = 2
        while not Fl or not Fr:
            Fl = self.polynomials(X=xl, Y=yl, degree=deg)
            Fr = self.polynomials(X=xr, Y=yr, degree=deg)
            deg += 1
        F += Fl + Fr

        return Sequence(F)


    def algebraic_differential_polynomials(self, a, b=None, order="deglex"):
        """
        Return a system of equations for algebraic-differential analysis.

        INPUT:

        - ``a`` -- input difference
        - ``b`` -- output difference (optional)
        - ``order`` -- monomial ordering (default : deglex)

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 3, 5, 8, 6, 10, 15, 4, 14, 13, 9, 2, 1, 7, 12, 11)
            sage: F = GS.algebraic_differential_polynomials(4, order="lex")
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
        """

        F = self.twoinput_polynomials()

        xl, xr = self.vars("xl"), self.vars("xr")
        m = self.input_size()
        if isinstance(a, integer_types + (Integer,)):
            a = self.to_bits(a, m)
        F += [ xl[i] + xr[i] + a[i] for i in range(m) ]

        if b is not None:
            yl, yr = self.vars("yl"), self.vars("yr")
            n = self.output_size()
            if isinstance(b, integer_types + (Integer,)):
                b = self.to_bits(b, n)
            F += [ yl[i] + yr[i] + b[i] for i in range(n) ]

        B = self.algebraic_differential_ring(order=order, use_polybori=True)

        return Sequence(F, B)


    def gb_linear_structures(self):
        """
        Return a tuple of (b, a, c) s.t. `a` is a `c`-linear structure of the
        component function `b \cdot S`.

        EXAMPLES::

            sage: from gbsbox import GBSBox
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
        B = self.algebraic_differential_ring(order="deglex", use_polybori=True)

        m, n = self.input_size(), self.output_size()
        xl, yl = self.vars("xl"), self.vars("yl")
        xr, yr = self.vars("xr"), self.vars("yr")

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


    def gb_differential_probability(self, a, b, get_numerator=False):
        """
        Return the differential probability of this S-Box.

        INPUT:

        - ``a`` - input difference
        - ``b`` - output difference
        - ``get_numerator`` - return only the numerator (default : False)

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: ddt = GS.difference_distribution_matrix()
            sage: ddt[1, 3] == GS.gb_differential_probability(1, 3, get_numerator=True)
            True
        """

        F = self.algebraic_differential_polynomials(a, b)
        G = F.groebner_basis()
        R = self.algebraic_differential_ring(order=G[0].parent().term_order(), use_polybori=False)
        I = Ideal(R, G) + FieldIdeal(R)
        num = I.vector_space_dimension()

        ret = 0
        if get_numerator:
            ret = num
        else:
            ret = num / (1 << self.input_size())

        return ret


    def gb_difference_distribution_matrix(self):
        """
        Return a difference distribution matrix using Grobner bases algorithm.

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: ddt = GS.difference_distribution_matrix()
            sage: gb_ddt = GS.gb_difference_distribution_matrix()
            sage: ddt == gb_ddt
            True
        """
        m, n = self.input_size(), self.output_size()
        nrows, ncols = 1 << m, 1 << n
        gbdp = self.gb_differential_probability
        entries = [ gbdp(a, b, get_numerator=True) for a in range(nrows) for b in range(ncols)]
        return Matrix(ZZ, entries, nrows=ncols, ncols=ncols)


    def gb_differential_uniformity(self):
        """
        Return the differential uniformity of this S-Box using Grobner bases algorithm.

        EXAMPLES::

            sage: from gbsbox import GBSBox
            sage: GS = GBSBox(0, 1, 3, 6, 7, 4, 5, 2)
            sage: GS.gb_differential_uniformity()
            2
        """
        m, n = self.input_size(), self.output_size()
        gbdp = self.gb_differential_probability

        d = max( gbdp(a, b, get_numerator=True) for a in range(1, 1<<m) for b in range(1<<n))

        return d
