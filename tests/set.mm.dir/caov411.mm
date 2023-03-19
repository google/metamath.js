include "co.mm"
include "caov31.mm"
include "oveq1i.mm"
include "ovex.mm"
include "caovass.mm"
include "3eqtr3i.mm"

theorem caov411
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let wph: wff ph
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cS: class S
  let cT: class T
  assume caov.1: |- A e. _V
  assume caov.2: |- B e. _V
  assume caov.3: |- C e. _V
  assume caov.com: |- ( x F y ) = ( y F x )
  assume caov.ass: |- ( ( x F y ) F z ) = ( x F ( y F z ) )
  assume caov.4: |- D e. _V

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
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint F x
  disjoint F y
  disjoint F z
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
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( A F B ) F ( C F D ) ) = ( ( C F B ) F ( A F D ) )

  proof
    cA
    cB
    cF
    co
    #
    cC
    cF
    co
    #
    cD
    cF
    co
    cC
    cB
    cF
    co
    #
    cA
    cF
    co
    #
    cD
    cF
    co
    @0
    cC
    cD
    cF
    co
    cF
    co
    @2
    cA
    cD
    cF
    co
    cF
    co
    @1
    @3
    cD
    cF
    vx
    vy
    vz
    cA
    cB
    cC
    cF
    caov.1
    caov.2
    caov.3
    caov.com
    caov.ass
    caov31
    oveq1i
    vx
    vy
    vz
    @0
    cC
    cD
    cF
    cA
    cB
    cF
    ovex
    caov.3
    caov.4
    caov.ass
    caovass
    vx
    vy
    vz
    @2
    cA
    cD
    cF
    cC
    cB
    cF
    ovex
    caov.1
    caov.4
    caov.ass
    caovass
    3eqtr3i
end
