include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "ralrimivvva.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem caovdig
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
  assume caovdig.1: |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) -> ( x G ( y F z ) ) = ( ( x G y ) H ( x G z ) ) )

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
  assert |- ( ( ph /\ ( A e. K /\ B e. S /\ C e. S ) ) -> ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cF
    co
    #
    cG
    co
    #
    @0
    @1
    cG
    co
    #
    @0
    @2
    cG
    co
    #
    cH
    co
    #
    wceq
    #
    vz
    cS
    wral
    vy
    cS
    wral
    vx
    cK
    wral
    cA
    cK
    wcel
    cB
    cS
    wcel
    cC
    cS
    wcel
    w3a
    cA
    cB
    cC
    cF
    co
    #
    cG
    co
    #
    cA
    cB
    cG
    co
    #
    cA
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
    cK
    cS
    cS
    caovdig.1
    ralrimivvva
    @8
    @14
    cA
    @3
    cG
    co
    #
    cA
    @1
    cG
    co
    #
    cA
    @2
    cG
    co
    #
    cH
    co
    #
    wceq
    cA
    cB
    @2
    cF
    co
    #
    cG
    co
    #
    @11
    @17
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
    cK
    cS
    cS
    @0
    cA
    wceq
    #
    @4
    @15
    @7
    @18
    @0
    cA
    @3
    cG
    oveq1
    @22
    @5
    @16
    @6
    @17
    cH
    @0
    cA
    @1
    cG
    oveq1
    @0
    cA
    @2
    cG
    oveq1
    oveq12d
    eqeq12d
    @1
    cB
    wceq
    #
    @15
    @20
    @18
    @21
    @23
    @3
    @19
    cA
    cG
    @1
    cB
    @2
    cF
    oveq1
    oveq2d
    @23
    @16
    @11
    @17
    cH
    @1
    cB
    cA
    cG
    oveq2
    oveq1d
    eqeq12d
    @2
    cC
    wceq
    #
    @20
    @10
    @21
    @13
    @24
    @19
    @9
    cA
    cG
    @2
    cC
    cB
    cF
    oveq2
    oveq2d
    @24
    @17
    @12
    @11
    cH
    @2
    cC
    cA
    cG
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    mpan9
end
