include "wcel.mm"
include "wbr.mm"
include "co.mm"
include "caovord.mm"
include "caovcom.mm"
include "breq12i.mm"
include "syl6bb.mm"

theorem caovord2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let cD: class D
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cT: class T
  assume caovord.1: |- A e. _V
  assume caovord.2: |- B e. _V
  assume caovord.3: |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) )
  assume caovord2.3: |- C e. _V
  assume caovord2.com: |- ( x F y ) = ( y F x )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( C e. S -> ( A R B <-> ( A F C ) R ( B F C ) ) )

  proof
    cC
    cS
    wcel
    cA
    cB
    cR
    wbr
    cC
    cA
    cF
    co
    #
    cC
    cB
    cF
    co
    #
    cR
    wbr
    cA
    cC
    cF
    co
    #
    cB
    cC
    cF
    co
    #
    cR
    wbr
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    cS
    cF
    caovord.1
    caovord.2
    caovord.3
    caovord
    @0
    @2
    @1
    @3
    cR
    vx
    vy
    cC
    cA
    cF
    caovord2.3
    caovord.1
    caovord2.com
    caovcom
    vx
    vy
    cC
    cB
    cF
    caovord2.3
    caovord.2
    caovord2.com
    caovcom
    breq12i
    syl6bb
end
