include "wcel.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wel.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cvv.mm"
include "wb.mm"
include "simpr.mm"
include "uniexg.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "tgss3.mm"
include "syldan.mm"
include "eltg2b.mm"
include "syl.mm"
include "elunii.mm"
include "ancoms.mm"
include "biimt.mm"
include "ralbidva.mm"
include "sylan9bb.mm"
include "ralcom3.mm"
include "syl6bb.mm"
include "dfss3.mm"
include "ralcom.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem tgss2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cV: class V
  let cJ: class J

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint V x
  disjoint V y
  disjoint J x
  disjoint J y
  disjoint J z
  assert |- ( ( B e. V /\ U. B = U. C ) -> ( ( topGen ` B ) C_ ( topGen ` C ) <-> A. x e. U. B A. y e. B ( x e. y -> E. z e. C ( x e. z /\ z C_ y ) ) ) )

  proof
    cB
    cV
    wcel
    #
    cB
    cuni
    #
    cC
    cuni
    #
    wceq
    #
    wa
    #
    cB
    ctg
    cfv
    cC
    ctg
    cfv
    #
    wss
    #
    cB
    @5
    wss
    #
    vx
    vy
    wel
    #
    vx
    vz
    wel
    vz
    cv
    vy
    cv
    #
    wss
    wa
    vz
    cC
    wrex
    #
    wi
    #
    vy
    cB
    wral
    vx
    @1
    wral
    #
    @0
    @3
    cC
    cvv
    wcel
    #
    @6
    @7
    wb
    @4
    @2
    cvv
    wcel
    @13
    @4
    @1
    @2
    cvv
    @0
    @3
    simpr
    @0
    @1
    cvv
    wcel
    @3
    cB
    cV
    uniexg
    adantr
    eqeltrrd
    cC
    uniexb
    sylibr
    #
    cB
    cC
    cV
    cvv
    tgss3
    syldan
    @4
    @9
    @5
    wcel
    #
    vy
    cB
    wral
    @11
    vx
    @1
    wral
    #
    vy
    cB
    wral
    @7
    @12
    @4
    @15
    @16
    vy
    cB
    @4
    @9
    cB
    wcel
    #
    wa
    @15
    vx
    cv
    #
    @1
    wcel
    #
    @10
    wi
    #
    vx
    @9
    wral
    #
    @16
    @4
    @15
    @10
    vx
    @9
    wral
    #
    @17
    @21
    @4
    @13
    @15
    @22
    wb
    @14
    vx
    vz
    @9
    cC
    cvv
    eltg2b
    syl
    @17
    @10
    @20
    vx
    @9
    @17
    @8
    wa
    @19
    @10
    @20
    wb
    @8
    @17
    @19
    @18
    @9
    cB
    elunii
    ancoms
    @19
    @10
    biimt
    syl
    ralbidva
    sylan9bb
    @10
    vx
    @9
    @1
    ralcom3
    syl6bb
    ralbidva
    vy
    cB
    @5
    dfss3
    @11
    vx
    vy
    @1
    cB
    ralcom
    3bitr4g
    bitrd
end
