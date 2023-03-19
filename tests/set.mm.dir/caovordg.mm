include "cv.mm"
include "wbr.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "wcel.mm"
include "w3a.mm"
include "ralrimivvva.mm"
include "wceq.mm"
include "breq1.mm"
include "oveq2.mm"
include "breq1d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "oveq1.mm"
include "breq12d.mm"
include "bibi2d.mm"
include "rspc3v.mm"
include "mpan9.mm"

theorem caovordg
  let wph: wff ph
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
  let cG: class G
  let cH: class H
  let cK: class K
  let cT: class T
  assume caovordg.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( x R y <-> ( z F x ) R ( z F y ) ) )

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
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
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
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( A R B <-> ( C F A ) R ( C F B ) ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vz
    cv
    #
    @0
    cF
    co
    #
    @3
    @1
    cF
    co
    #
    cR
    wbr
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
    cS
    wral
    cA
    cS
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
    cR
    wbr
    #
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
    #
    wb
    #
    wph
    @7
    vx
    vy
    vz
    cS
    cS
    cS
    caovordg.1
    ralrimivvva
    @7
    @12
    cA
    @1
    cR
    wbr
    #
    @3
    cA
    cF
    co
    #
    @5
    cR
    wbr
    #
    wb
    @8
    @14
    @3
    cB
    cF
    co
    #
    cR
    wbr
    #
    wb
    vx
    vy
    vz
    cA
    cB
    cC
    cS
    cS
    cS
    @0
    cA
    wceq
    #
    @2
    @13
    @6
    @15
    @0
    cA
    @1
    cR
    breq1
    @18
    @4
    @14
    @5
    cR
    @0
    cA
    @3
    cF
    oveq2
    breq1d
    bibi12d
    @1
    cB
    wceq
    #
    @13
    @8
    @15
    @17
    @1
    cB
    cA
    cR
    breq2
    @19
    @5
    @16
    @14
    cR
    @1
    cB
    @3
    cF
    oveq2
    breq2d
    bibi12d
    @3
    cC
    wceq
    #
    @17
    @11
    @8
    @20
    @14
    @9
    @16
    @10
    cR
    @3
    cC
    cA
    cF
    oveq1
    @3
    cC
    cB
    cF
    oveq1
    breq12d
    bibi2d
    rspc3v
    mpan9
end
