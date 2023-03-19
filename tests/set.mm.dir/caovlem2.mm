include "co.mm"
include "ovex.mm"
include "caov42.mm"
include "caovdilem.mm"
include "oveq12i.mm"
include "caovdi.mm"
include "3eqtr4i.mm"

theorem caovlem2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
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
  assume caovdl2.6: |- R e. _V
  assume caovdl2.com: |- ( x F y ) = ( y F x )
  assume caovdl2.ass: |- ( ( x F y ) F z ) = ( x F ( y F z ) )

  disjoint x y
  disjoint x z
  disjoint H x
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint R x
  disjoint R y
  disjoint R z
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
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( ( ( A G C ) F ( B G D ) ) G H ) F ( ( ( A G D ) F ( B G C ) ) G R ) ) = ( ( A G ( ( C G H ) F ( D G R ) ) ) F ( B G ( ( C G R ) F ( D G H ) ) ) )

  proof
    cA
    cC
    cH
    cG
    co
    #
    cG
    co
    #
    cB
    cD
    cH
    cG
    co
    #
    cG
    co
    #
    cF
    co
    #
    cA
    cD
    cR
    cG
    co
    #
    cG
    co
    #
    cB
    cC
    cR
    cG
    co
    #
    cG
    co
    #
    cF
    co
    #
    cF
    co
    @1
    @6
    cF
    co
    #
    @8
    @3
    cF
    co
    #
    cF
    co
    cA
    cC
    cG
    co
    cB
    cD
    cG
    co
    cF
    co
    cH
    cG
    co
    #
    cA
    cD
    cG
    co
    cB
    cC
    cG
    co
    cF
    co
    cR
    cG
    co
    #
    cF
    co
    cA
    @0
    @5
    cF
    co
    cG
    co
    #
    cB
    @7
    @2
    cF
    co
    cG
    co
    #
    cF
    co
    vx
    vy
    vz
    @1
    @3
    @6
    @8
    cF
    cA
    @0
    cG
    ovex
    cB
    @2
    cG
    ovex
    cA
    @5
    cG
    ovex
    caovdl2.com
    caovdl2.ass
    cB
    @7
    cG
    ovex
    caov42
    @12
    @4
    @13
    @9
    cF
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    cF
    cG
    cH
    caovdir.1
    caovdir.2
    caovdir.3
    caovdir.com
    caovdir.distr
    caovdl.4
    caovdl.5
    caovdl.ass
    caovdilem
    vx
    vy
    vz
    cA
    cB
    cD
    cC
    cF
    cG
    cR
    caovdir.1
    caovdir.2
    caovdl.4
    caovdir.com
    caovdir.distr
    caovdir.3
    caovdl2.6
    caovdl.ass
    caovdilem
    oveq12i
    @14
    @10
    @15
    @11
    cF
    vx
    vy
    vz
    cA
    @0
    @5
    cF
    cG
    caovdir.1
    cC
    cH
    cG
    ovex
    cD
    cR
    cG
    ovex
    caovdir.distr
    caovdi
    vx
    vy
    vz
    cB
    @7
    @2
    cF
    cG
    caovdir.2
    cC
    cR
    cG
    ovex
    cD
    cH
    cG
    ovex
    caovdir.distr
    caovdi
    oveq12i
    3eqtr4i
end
