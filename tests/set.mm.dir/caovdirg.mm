include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "ralrimivvva.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem caovdirg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cD: class D
  let cR: class R
  let cT: class T
  assume caovdirg.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) -> ( ( x F y ) G z ) = ( ( x G z ) H ( y G z ) ) )

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
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. K ) ) -> ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    vz
    cv
    #
    cG
    co
    #
    @0
    @3
    cG
    co
    #
    @1
    @3
    cG
    co
    #
    cH
    co
    #
    wceq
    #
    vz
    cK
    wral
    vy
    cS
    wral
    vx
    cS
    wral
    cA
    cS
    wcel
    cB
    cS
    wcel
    cC
    cK
    wcel
    w3a
    cA
    cB
    cF
    co
    #
    cC
    cG
    co
    #
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
    cH
    co
    #
    wceq
    #
    wph
    @8
    vx
    vy
    vz
    cS
    cS
    cK
    caovdirg.1
    ralrimivvva
    @8
    @14
    cA
    @1
    cF
    co
    #
    @3
    cG
    co
    #
    cA
    @3
    cG
    co
    #
    @6
    cH
    co
    #
    wceq
    @9
    @3
    cG
    co
    #
    @17
    cB
    @3
    cG
    co
    #
    cH
    co
    #
    wceq
    vx
    vy
    vz
    cA
    cB
    cC
    cS
    cS
    cK
    @0
    cA
    wceq
    #
    @4
    @16
    @7
    @18
    @22
    @2
    @15
    @3
    cG
    @0
    cA
    @1
    cF
    oveq1
    oveq1d
    @22
    @5
    @17
    @6
    cH
    @0
    cA
    @3
    cG
    oveq1
    oveq1d
    eqeq12d
    @1
    cB
    wceq
    #
    @16
    @19
    @18
    @21
    @23
    @15
    @9
    @3
    cG
    @1
    cB
    cA
    cF
    oveq2
    oveq1d
    @23
    @6
    @20
    @17
    cH
    @1
    cB
    @3
    cG
    oveq1
    oveq2d
    eqeq12d
    @3
    cC
    wceq
    #
    @19
    @10
    @21
    @13
    @3
    cC
    @9
    cG
    oveq2
    @24
    @17
    @11
    @20
    @12
    cH
    @3
    cC
    cA
    cG
    oveq2
    @3
    cC
    cB
    cG
    oveq2
    oveq12d
    eqeq12d
    rspc3v
    mpan9
end
