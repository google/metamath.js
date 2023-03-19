include "wfr.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "cv.mm"
include "cpr.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "prex.mm"
include "a1i.mm"
include "simpl.mm"
include "prssi.mm"
include "adantl.mm"
include "prnzg.mm"
include "ad2antrl.mm"
include "fri.mm"
include "syl22anc.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rexprg.mm"
include "mpbid.mm"
include "wi.mm"
include "prid2g.mm"
include "ad2antll.mm"
include "breq1.mm"
include "rspcv.mm"
include "syl.mm"
include "prid1g.mm"
include "orim12d.mm"
include "mpd.mm"
include "orcomd.mm"
include "ianor.mm"
include "sylibr.mm"

theorem fr2nr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R Fr A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) )

  proof
    cA
    cR
    wfr
    #
    cB
    cA
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    #
    wa
    #
    cB
    cC
    cR
    wbr
    #
    wn
    #
    cC
    cB
    cR
    wbr
    #
    wn
    #
    wo
    @5
    @7
    wa
    wn
    @4
    @8
    @6
    @4
    vx
    cv
    #
    cB
    cR
    wbr
    #
    wn
    #
    vx
    cB
    cC
    cpr
    #
    wral
    #
    @9
    cC
    cR
    wbr
    #
    wn
    #
    vx
    @12
    wral
    #
    wo
    #
    @8
    @6
    wo
    @4
    @9
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vx
    @12
    wral
    #
    vy
    @12
    wrex
    #
    @17
    @4
    @12
    cvv
    wcel
    #
    @0
    @12
    cA
    wss
    #
    @12
    c0
    wne
    #
    @22
    @23
    @4
    cB
    cC
    prex
    a1i
    @0
    @3
    simpl
    @3
    @24
    @0
    cB
    cC
    cA
    prssi
    adantl
    @1
    @25
    @0
    @2
    cB
    cC
    cA
    prnzg
    ad2antrl
    vy
    vx
    cA
    @12
    cvv
    cR
    fri
    syl22anc
    @3
    @22
    @17
    wb
    @0
    @21
    @13
    @16
    vy
    cB
    cC
    cA
    cA
    @18
    cB
    wceq
    #
    @20
    @11
    vx
    @12
    @26
    @19
    @10
    @18
    cB
    @9
    cR
    breq2
    notbid
    ralbidv
    @18
    cC
    wceq
    #
    @20
    @15
    vx
    @12
    @27
    @19
    @14
    @18
    cC
    @9
    cR
    breq2
    notbid
    ralbidv
    rexprg
    adantl
    mpbid
    @4
    @13
    @8
    @16
    @6
    @4
    cC
    @12
    wcel
    #
    @13
    @8
    wi
    @2
    @28
    @0
    @1
    cB
    cC
    cA
    prid2g
    ad2antll
    @11
    @8
    vx
    cC
    @12
    @9
    cC
    wceq
    @10
    @7
    @9
    cC
    cB
    cR
    breq1
    notbid
    rspcv
    syl
    @4
    cB
    @12
    wcel
    #
    @16
    @6
    wi
    @1
    @29
    @0
    @2
    cB
    cC
    cA
    prid1g
    ad2antrl
    @15
    @6
    vx
    cB
    @12
    @9
    cB
    wceq
    @14
    @5
    @9
    cB
    cC
    cR
    breq1
    notbid
    rspcv
    syl
    orim12d
    mpd
    orcomd
    @5
    @7
    ianor
    sylibr
end
