include "csur.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "cfv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cdm.mm"
include "cun.mm"
include "wa.mm"
include "cslt.mm"
include "wbr.mm"
include "wo.mm"
include "wor.mm"
include "wb.mm"
include "sltso.mm"
include "sotrine.mm"
include "mpan.mm"
include "nosepdmlem.mm"
include "3expa.mm"
include "simplr.mm"
include "simpll.mm"
include "simpr.mm"
include "syl3anc.mm"
include "necom.mm"
include "rabbii.mm"
include "inteqi.mm"
include "uncom.mm"
include "3eltr4g.mm"
include "jaodan.mm"
include "ex.mm"
include "sylbid.mm"
include "3impia.mm"

theorem nosepdm
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. No /\ B e. No /\ A =/= B ) -> |^| { x e. On | ( A ` x ) =/= ( B ` x ) } e. ( dom A u. dom B ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cA
    cB
    wne
    #
    vx
    cv
    #
    cA
    cfv
    #
    @3
    cB
    cfv
    #
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    cA
    cdm
    #
    cB
    cdm
    #
    cun
    #
    wcel
    #
    @0
    @1
    wa
    #
    @2
    cA
    cB
    cslt
    wbr
    #
    cB
    cA
    cslt
    wbr
    #
    wo
    #
    @12
    csur
    cslt
    wor
    @13
    @2
    @16
    wb
    sltso
    csur
    cA
    cB
    cslt
    sotrine
    mpan
    @13
    @16
    @12
    @13
    @14
    @12
    @15
    @0
    @1
    @14
    @12
    vx
    cA
    cB
    nosepdmlem
    3expa
    @13
    @15
    wa
    #
    @5
    @4
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    @10
    @9
    cun
    #
    @8
    @11
    @17
    @1
    @0
    @15
    @20
    @21
    wcel
    @0
    @1
    @15
    simplr
    @0
    @1
    @15
    simpll
    @13
    @15
    simpr
    vx
    cB
    cA
    nosepdmlem
    syl3anc
    @7
    @19
    @6
    @18
    vx
    con0
    @4
    @5
    necom
    rabbii
    inteqi
    @9
    @10
    uncom
    3eltr4g
    jaodan
    ex
    sylbid
    3impia
end
