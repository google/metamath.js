include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "ralrimivvva.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "bibi1d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem caovcang
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cD: class D
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  assume caovcang.1: |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) -> ( ( x F y ) = ( x F z ) <-> y = z ) )

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
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint D x
  disjoint D y
  disjoint D z
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
  assert |- ( ( ph /\ ( A e. T /\ B e. S /\ C e. S ) ) -> ( ( A F B ) = ( A F C ) <-> B = C ) )

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
    @0
    vz
    cv
    #
    cF
    co
    #
    wceq
    #
    @1
    @3
    wceq
    #
    wb
    #
    vz
    cS
    wral
    vy
    cS
    wral
    vx
    cT
    wral
    cA
    cT
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
    cF
    co
    #
    cA
    cC
    cF
    co
    #
    wceq
    #
    cB
    cC
    wceq
    #
    wb
    #
    wph
    @7
    vx
    vy
    vz
    cT
    cS
    cS
    caovcang.1
    ralrimivvva
    @7
    @12
    cA
    @1
    cF
    co
    #
    cA
    @3
    cF
    co
    #
    wceq
    #
    @6
    wb
    @8
    @14
    wceq
    #
    cB
    @3
    wceq
    #
    wb
    vx
    vy
    vz
    cA
    cB
    cC
    cT
    cS
    cS
    @0
    cA
    wceq
    #
    @5
    @15
    @6
    @18
    @2
    @13
    @4
    @14
    @0
    cA
    @1
    cF
    oveq1
    @0
    cA
    @3
    cF
    oveq1
    eqeq12d
    bibi1d
    @1
    cB
    wceq
    #
    @15
    @16
    @6
    @17
    @19
    @13
    @8
    @14
    @1
    cB
    cA
    cF
    oveq2
    eqeq1d
    @1
    cB
    @3
    eqeq1
    bibi12d
    @3
    cC
    wceq
    #
    @16
    @10
    @17
    @11
    @20
    @14
    @9
    @8
    @3
    cC
    cA
    cF
    oveq2
    eqeq2d
    @3
    cC
    cB
    eqeq2
    bibi12d
    rspc3v
    mpan9
end
