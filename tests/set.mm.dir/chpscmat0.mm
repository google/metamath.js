include "co.mm"
include "chpscmat.mm"

theorem chpscmat0
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let vc: setvar c
  let vk: setvar k
  let cE: class E
  let vl: setvar l
  let cF: class F
  let cJ: class J
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume chp0mat.c: |- C = ( N CharPlyMat R )
  assume chp0mat.p: |- P = ( Poly1 ` R )
  assume chp0mat.a: |- A = ( N Mat R )
  assume chp0mat.x: |- X = ( var1 ` R )
  assume chp0mat.g: |- G = ( mulGrp ` P )
  assume chp0mat.m: |- .^ = ( .g ` G )
  assume chpscmat.d: |- D = { m e. ( Base ` A ) | E. c e. ( Base ` R ) A. i e. N A. j e. N ( i m j ) = if ( i = j , c , ( 0g ` R ) ) }
  assume chpscmat.s: |- S = ( algSc ` P )
  assume chpscmat.m: |- .- = ( -g ` P )

  disjoint A c
  disjoint A m
  disjoint c m
  disjoint D n
  disjoint I n
  disjoint M c
  disjoint M i
  disjoint M j
  disjoint M m
  disjoint M n
  disjoint c i
  disjoint c j
  disjoint c n
  disjoint i j
  disjoint i m
  disjoint i n
  disjoint j m
  disjoint j n
  disjoint m n
  disjoint N c
  disjoint N m
  disjoint N n
  disjoint P n
  disjoint R c
  disjoint R m
  disjoint R n
  disjoint S n
  disjoint i j
  disjoint A i
  disjoint A j
  disjoint N i
  disjoint N j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint X i
  disjoint X j
  disjoint D k
  disjoint k n
  disjoint E k
  disjoint E n
  disjoint I k
  disjoint M k
  disjoint c k
  disjoint i k
  disjoint j k
  disjoint k m
  disjoint S k
  disjoint .- k
  disjoint D l
  disjoint F l
  disjoint I l
  disjoint J l
  disjoint J n
  disjoint l n
  disjoint M l
  disjoint N l
  disjoint P l
  disjoint R l
  disjoint S l
  disjoint X l
  disjoint .^ l
  disjoint .0. i
  disjoint .0. j
  disjoint .0. k
  disjoint i k
  disjoint j k
  disjoint A k
  disjoint G k
  disjoint N k
  disjoint N x
  disjoint N y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint P k
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint X k
  assert |- ( ( ( N e. Fin /\ R e. CRing ) /\ ( M e. D /\ I e. N /\ A. n e. N ( n M n ) = ( I M I ) ) ) -> ( C ` M ) = ( ( # ` N ) .^ ( X .- ( S ` ( I M I ) ) ) ) )

  proof
    cA
    cC
    cD
    cP
    cR
    cS
    vi
    vj
    vm
    vn
    cI
    cI
    cM
    co
    c.ex
    cG
    cI
    cM
    c.mi
    cN
    cX
    vc
    chp0mat.c
    chp0mat.p
    chp0mat.a
    chp0mat.x
    chp0mat.g
    chp0mat.m
    chpscmat.d
    chpscmat.s
    chpscmat.m
    chpscmat
end
