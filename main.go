package main

import (
	"flag"
	"fmt"
	"math/big"
	"sort"
)

var (
	stPeriod = flag.Int("s_t_period", 40, "Orbifolds for sphere and torus will be generated up to this period.")
	maxG     = flag.Int("max_g", 50, "Max surface genus.")
	big0     = big.NewInt(0)
	big1     = big.NewInt(1)
)

// divisors is a cache for Divisors function
var divisors [][]int

// Divisors returns a slice of positive divisors of a positive integer n
func Divisors(n int) []int {
	for len(divisors) <= n {
		divisors = append(divisors, nil)
	}
	if divisors[n] == nil {
		for j := 1; j*j <= n; j++ {
			if n%j != 0 {
				continue
			}
			divisors[n] = append(divisors[n], j)
			if j*j != n {
				divisors[n] = append(divisors[n], n/j)
			}
		}
		sort.Ints(divisors[n])
	}
	return divisors[n]
}

// j is a cache for J function
var j [][]*big.Int

// J is the k-th Jordan's totient function of n
func J(k, n int) *big.Int {
	for len(j) <= k {
		j = append(j, nil)
	}
	for len(j[k]) <= n {
		j[k] = append(j[k], nil)
	}
	if j[k][n] == nil {
		bigK := big.NewInt(int64(k))
		bigN := big.NewInt(int64(n))
		j[k][n] = new(big.Int).Exp(bigN, bigK, big0)
		for _, p := range Divisors(n) {
			if len(Divisors(p)) != 2 {
				continue
			}
			bigP := big.NewInt(int64(p))
			bigPK := new(big.Int).Exp(bigP, bigK, big0)
			j[k][n].Div(j[k][n], bigPK)
			j[k][n].Mul(j[k][n], new(big.Int).Sub(bigPK, big1))
		}
	}
	return j[k][n]
}

// Phi is the Euler's function of n
func Phi(n int) *big.Int {
	return J(1, n)
}

// covering is a signature of a periodic covering of a surface
// by an orientable surface without a boundary arising from
// an orientation-reversing automorphism
type covering struct {
	G, L, g, h int
	orientable bool
	m          []int
}

// Sign returns "+" if the covered surface is orientable and "-" otherwise
func (c *covering) Sign() string {
	if !c.orientable {
		return "-"
	}
	return "+"
}

// lcm computes the least common multiple of given integers
func lcm(nums ...int) int {
	lcm := 1
	for _, m := range nums {
		var d int
		for i := 1; i <= m; i++ {
			if lcm%i == 0 && m%i == 0 {
				d = i
			}
		}
		lcm = lcm * m / d
	}
	return lcm
}

// Chi returns the Euler characteristic of the covered surface
func (c *covering) Chi() int {
	return 2 - c.h - c.g
}

// EpiPlus returns the number of orientation-and-order-preserving epimorphisms from the NEC group of
// the covered surface onto the cyclic group Z_{L} (L even) endowed with a sign structure that
// assigns "-1" to odd elements and "+1" to even ones.
func (c *covering) EpiPlus() *big.Int {
	res := new(big.Int)
	m := lcm(c.m...)
	switch {
	case c.orientable && c.h == 0:
	case !c.orientable && c.g == 0:
	case c.orientable && c.g%2 != 0:
	case c.h == 0 && c.L%4 == 0 && !c.orientable:
		var s int
		for _, m := range c.m {
			s += c.L / 2 / m
		}
		if (s+c.g)%2 == 1 {
			break
		}
		res.Add(res, big1)
		fallthrough
	case c.L%4 == 2:
		L, p2 := c.L/2, 1
		for L%2 == 0 {
			L, p2 = L/2, p2*2
		}
		m = lcm(m, p2)
		res.Add(res, big1)
		res.Mul(res, J(c.g+c.h-1, c.L/2/m))
	}
	res.Mul(res, new(big.Int).Exp(big.NewInt(int64(m)), big.NewInt(int64(c.g+c.h-1)), big0))
	for _, m := range c.m {
		res.Mul(res, Phi(m))
	}
	return res
}

// String returns a machine-and-human-readable representation of the signature
// together with the value of EpiPlus.
func (c *covering) String() string {
	return fmt.Sprintf("%3d %3d [%s] %3d %2d %v %s", c.G, c.L, c.Sign(), c.Chi(), c.h, c.m, c.EpiPlus())
}

// ORCoverings iterates over all coverings with period 2*halfL of surfaces with
// Euler characteristic Chi by genus G orientable surfaces without a boundary
// and calls f for each covering with a non-zero number of
// orientation-and-order-preserving epimorphisms.
// "rem" and "m" parameters are used in recursive calls to track
// the enumeration of branch points.
// Initially "rem" should be equal to 2*(halfL + G - 1), "m" should be empty.
func ORCoverings(G, Chi, halfL, rem int, f func(covering), m ...int) {
	if rem < 0 {
		return
	}
	if rem == 0 {
		mc := make([]int, len(m))
		copy(mc, m)
		for _, orientable := range []bool{true, false} {
			for h := 0; h <= 2-Chi; h++ {
				cov := covering{G: G, L: 2 * halfL, m: mc, orientable: orientable, h: h, g: 2 - Chi - h}
				if cov.EpiPlus().Cmp(big0) != 0 {
					f(cov)
				}
			}
		}
		return
	}
	next := 2
	if len(m) > 0 {
		next = m[len(m)-1]
	}
	for _, d := range Divisors(halfL) {
		if d < next {
			continue
		}
		ORCoverings(G, Chi, halfL, rem-(2*halfL-2*halfL/d), f, append(m, d)...)
	}
}

func main() {
	fmt.Println(`# Format: G L [O] Chi H [m1 ... mr] E, where:
#
# G: Genus of the covering surface.
# L: Cyclic covering period.
# O: Sign, "+" for orientable orbifolds and "-" for non-orientable ones.
# Chi: Euler characteristics of the covered surface.
# H: Number of boundary components in the covered surface. If O is "-", the number of crosscaps is 2 - Chi - H; is O is "+", the number of handles is (2 - Chi - H) / 2.
# [m1 ... mr]: Branch point indices.
# E: Number of orientation-and-order-preserving epimorphisms from the F-group of the orbifold onto Z_L endowed with non-trivial sign structure.
`)
	for G := 0; G <= *maxG; G++ {
		maxL := 4*G + 4
		if G <= 1 {
			maxL = *stPeriod
		}
		for L := 2; L <= maxL; L += 2 {
			for Chi := 1; Chi >= 1-G; Chi-- {
				ORCoverings(G, Chi, L/2, L*Chi+2*G-2, func(c covering) {
					fmt.Println(c.String())
				})
			}
		}
		if G <= 1 {
			fmt.Printf("# .... <infinite series for G = %d truncated to L = %d>\n", G, *stPeriod)
		}
	}
}
