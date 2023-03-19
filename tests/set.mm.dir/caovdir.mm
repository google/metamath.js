include "co.mm"
include "caovdi.mm"
include "ovex.mm"
include "caovcom.mm"
include "oveq12i.mm"
include "3eqtr3i.mm"

theorem caovdir
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cD: class D
  let wph: wff ph
  let cH: class H
  let cK: class K
  let cR: class R
  let cS: class S
  let cT: class T
  assume caovdir.1: |- A e. _V
  assume caovdir.2: |- B e. _V
  assume caovdir.3: |- C e. _V
  assume caovdir.com: |- ( x G y ) = ( y G x )
  assume caovdir.distr: |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) )

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
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint ph x
  disjoint ph y
  disjoint ph z
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
  assert |- ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) )

  proof
    cC
    cA
    cB
    cF
    co
    #
    cG
    co
    cC
    cA
    cG
    co
    #
    cC
    cB
    cG
    co
    #
    cF
    co
    @0
    cC
    cG
    co
    cA
    cC
    cG
    co
    #
    cB
    cC
    cG
    co
    #
    cF
    co
    vx
    vy
    vz
    cC
    cA
    cB
    cF
    cG
    caovdir.3
    caovdir.1
    caovdir.2
    caovdir.distr
    caovdi
    vx
    vy
    cC
    @0
    cG
    caovdir.3
    cA
    cB
    cF
    ovex
    caovdir.com
    caovcom
    @1
    @3
    @2
    @4
    cF
    vx
    vy
    cC
    cA
    cG
    caovdir.3
    caovdir.1
    caovdir.com
    caovcom
    vx
    vy
    cC
    cB
    cG
    caovdir.3
    caovdir.2
    caovdir.com
    caovcom
    oveq12i
    3eqtr3i
end
