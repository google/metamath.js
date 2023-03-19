include "co.mm"
include "caovcom.mm"
include "oveq2i.mm"
include "caovass.mm"
include "3eqtr4i.mm"

theorem caov32
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cD: class D
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
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( A F B ) F C ) = ( ( A F C ) F B )

  proof
    cA
    cB
    cC
    cF
    co
    #
    cF
    co
    cA
    cC
    cB
    cF
    co
    #
    cF
    co
    cA
    cB
    cF
    co
    cC
    cF
    co
    cA
    cC
    cF
    co
    cB
    cF
    co
    @0
    @1
    cA
    cF
    vx
    vy
    cB
    cC
    cF
    caov.2
    caov.3
    caov.com
    caovcom
    oveq2i
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
    caov.ass
    caovass
    vx
    vy
    vz
    cA
    cC
    cB
    cF
    caov.1
    caov.3
    caov.2
    caov.ass
    caovass
    3eqtr4i
end
