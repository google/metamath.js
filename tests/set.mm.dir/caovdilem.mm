include "co.mm"
include "ovex.mm"
include "caovdir.mm"
include "caovass.mm"
include "oveq12i.mm"
include "eqtri.mm"

theorem caovdilem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let cR: class R
  let wph: wff ph
  let cK: class K
  let cS: class S
  let cT: class T
  assume caovdir.1: |- A e. _V
  assume caovdir.2: |- B e. _V
  assume caovdir.3: |- C e. _V
  assume caovdir.com: |- ( x G y ) = ( y G x )
  assume caovdir.distr: |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) )
  assume caovdl.4: |- D e. _V
  assume caovdl.5: |- H e. _V
  assume caovdl.ass: |- ( ( x G y ) G z ) = ( x G ( y G z ) )

  disjoint x y
  disjoint x z
  disjoint H x
  disjoint y z
  disjoint H y
  disjoint H z
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
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint ph x
  disjoint ph y
  disjoint ph z
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
  assert |- ( ( ( A G C ) F ( B G D ) ) G H ) = ( ( A G ( C G H ) ) F ( B G ( D G H ) ) )

  proof
    cA
    cC
    cG
    co
    #
    cB
    cD
    cG
    co
    #
    cF
    co
    cH
    cG
    co
    @0
    cH
    cG
    co
    #
    @1
    cH
    cG
    co
    #
    cF
    co
    cA
    cC
    cH
    cG
    co
    cG
    co
    #
    cB
    cD
    cH
    cG
    co
    cG
    co
    #
    cF
    co
    vx
    vy
    vz
    @0
    @1
    cH
    cF
    cG
    cA
    cC
    cG
    ovex
    cB
    cD
    cG
    ovex
    caovdl.5
    caovdir.com
    caovdir.distr
    caovdir
    @2
    @4
    @3
    @5
    cF
    vx
    vy
    vz
    cA
    cC
    cH
    cG
    caovdir.1
    caovdir.3
    caovdl.5
    caovdl.ass
    caovass
    vx
    vy
    vz
    cB
    cD
    cH
    cG
    caovdir.2
    caovdl.4
    caovdl.5
    caovdl.ass
    caovass
    oveq12i
    eqtri
end
