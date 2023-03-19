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
include "rspc3v.mm"
include "mpan9.mm"

theorem caovassg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cF: class F
  let cD: class D
  let cG: class G
  let cH: class H
  let cK: class K
  let cR: class R
  let cT: class T
  assume caovassg.1: |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) -> ( ( x F y ) F z ) = ( x F ( y F z ) ) )

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
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) -> ( ( A F B ) F C ) = ( A F ( B F C ) ) )

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
    cF
    co
    #
    @0
    @1
    @3
    cF
    co
    #
    cF
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
    cF
    co
    #
    cC
    cF
    co
    #
    cA
    cB
    cC
    cF
    co
    #
    cF
    co
    #
    wceq
    #
    wph
    @7
    vx
    vy
    vz
    cS
    cS
    cS
    caovassg.1
    ralrimivvva
    @7
    @12
    cA
    @1
    cF
    co
    #
    @3
    cF
    co
    #
    cA
    @5
    cF
    co
    #
    wceq
    @8
    @3
    cF
    co
    #
    cA
    cB
    @3
    cF
    co
    #
    cF
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
    cS
    @0
    cA
    wceq
    #
    @4
    @14
    @6
    @15
    @19
    @2
    @13
    @3
    cF
    @0
    cA
    @1
    cF
    oveq1
    oveq1d
    @0
    cA
    @5
    cF
    oveq1
    eqeq12d
    @1
    cB
    wceq
    #
    @14
    @16
    @15
    @18
    @20
    @13
    @8
    @3
    cF
    @1
    cB
    cA
    cF
    oveq2
    oveq1d
    @20
    @5
    @17
    cA
    cF
    @1
    cB
    @3
    cF
    oveq1
    oveq2d
    eqeq12d
    @3
    cC
    wceq
    #
    @16
    @9
    @18
    @11
    @3
    cC
    @8
    cF
    oveq2
    @21
    @17
    @10
    cA
    cF
    @3
    cC
    cB
    cF
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    mpan9
end
