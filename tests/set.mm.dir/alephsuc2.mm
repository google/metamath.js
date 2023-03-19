include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "cale.mm"
include "cfv.mm"
include "cdom.mm"
include "wbr.mm"
include "crab.mm"
include "csuc.mm"
include "csdm.mm"
include "alephsucdom.mm"
include "rabbidv.mm"
include "wa.mm"
include "alephon.mm"
include "oneli.mm"
include "wral.mm"
include "ccrd.mm"
include "wceq.mm"
include "alephcard.mm"
include "iscard.mm"
include "mpbi.mm"
include "simpri.mm"
include "rspec.mm"
include "jca.mm"
include "wi.mm"
include "sdomel.mm"
include "mpan2.mm"
include "imp.mm"
include "impbii.mm"
include "breq1.mm"
include "elrab.mm"
include "bitr4i.mm"
include "eqriv.mm"
include "syl6reqr.mm"

theorem alephsuc2
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  assert |- ( A e. On -> ( aleph ` suc A ) = { x e. On | x ~<_ ( aleph ` A ) } )

  proof
    cA
    con0
    wcel
    #
    vx
    cv
    #
    cA
    cale
    cfv
    cdom
    wbr
    #
    vx
    con0
    crab
    @1
    cA
    csuc
    #
    cale
    cfv
    #
    csdm
    wbr
    #
    vx
    con0
    crab
    #
    @4
    @0
    @2
    @5
    vx
    con0
    @1
    cA
    alephsucdom
    rabbidv
    vy
    @4
    @6
    vy
    cv
    #
    @4
    wcel
    #
    @7
    con0
    wcel
    #
    @7
    @4
    csdm
    wbr
    #
    wa
    #
    @7
    @6
    wcel
    @8
    @11
    @8
    @9
    @10
    @4
    @7
    @3
    alephon
    #
    oneli
    @10
    vy
    @4
    @4
    con0
    wcel
    #
    @10
    vy
    @4
    wral
    #
    @4
    ccrd
    cfv
    @4
    wceq
    @13
    @14
    wa
    @3
    alephcard
    vy
    @4
    iscard
    mpbi
    simpri
    rspec
    jca
    @9
    @10
    @8
    @9
    @13
    @10
    @8
    wi
    @12
    @7
    @4
    sdomel
    mpan2
    imp
    impbii
    @5
    @10
    vx
    @7
    con0
    @1
    @7
    @4
    csdm
    breq1
    elrab
    bitr4i
    eqriv
    syl6reqr
end
