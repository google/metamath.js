include "csur.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "con0.mm"
include "wrex.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "wral.mm"
include "df-ne.mm"
include "rexbii.mm"
include "notbii.mm"
include "dfral2.mm"
include "bitr4i.mm"
include "cdm.mm"
include "wo.mm"
include "w3o.mm"
include "word.mm"
include "nodmord.mm"
include "ordtri3or.mm"
include "syl2an.mm"
include "3orass.mm"
include "or12.mm"
include "bitri.mm"
include "sylib.mm"
include "ord.mm"
include "noseponlem.mm"
include "3expia.mm"
include "wi.mm"
include "eqcom.mm"
include "ralbii.mm"
include "sylnibr.mm"
include "ancoms.mm"
include "jaod.mm"
include "syld.mm"
include "con4d.mm"
include "3impia.mm"
include "wss.mm"
include "ordsson.mm"
include "ssralv.mm"
include "3syl.mm"
include "adantr.mm"
include "wfun.mm"
include "wb.mm"
include "nofun.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "eqfunfv.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "syl5bi.mm"
include "necon1ad.mm"
include "onintrab2.mm"

theorem nosepon
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. No /\ B e. No /\ A =/= B ) -> |^| { x e. On | ( A ` x ) =/= ( B ` x ) } e. On )

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
    w3a
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
    wrex
    #
    @6
    vx
    con0
    crab
    cint
    con0
    wcel
    @0
    @1
    @2
    @7
    @0
    @1
    wa
    #
    @7
    cA
    cB
    @7
    wn
    #
    @4
    @5
    wceq
    #
    vx
    con0
    wral
    #
    @8
    cA
    cB
    wceq
    #
    @9
    @10
    wn
    #
    vx
    con0
    wrex
    #
    wn
    @11
    @7
    @14
    @6
    @13
    vx
    con0
    @4
    @5
    df-ne
    rexbii
    notbii
    @10
    vx
    con0
    dfral2
    bitr4i
    @0
    @1
    @11
    @12
    @0
    @1
    @11
    w3a
    #
    @12
    cA
    cdm
    #
    cB
    cdm
    #
    wceq
    #
    @10
    vx
    @16
    wral
    #
    @0
    @1
    @11
    @18
    @8
    @18
    @11
    @8
    @18
    wn
    @16
    @17
    wcel
    #
    @17
    @16
    wcel
    #
    wo
    #
    @11
    wn
    #
    @8
    @18
    @22
    @8
    @20
    @18
    @21
    w3o
    #
    @18
    @22
    wo
    #
    @0
    @16
    word
    #
    @17
    word
    @24
    @1
    cA
    nodmord
    #
    cB
    nodmord
    @16
    @17
    ordtri3or
    syl2an
    @24
    @20
    @18
    @21
    wo
    wo
    @25
    @20
    @18
    @21
    3orass
    @20
    @18
    @21
    or12
    bitri
    sylib
    ord
    @8
    @20
    @23
    @21
    @0
    @1
    @20
    @23
    vx
    cA
    cB
    noseponlem
    3expia
    @1
    @0
    @21
    @23
    wi
    @1
    @0
    @21
    @23
    @1
    @0
    @21
    w3a
    @5
    @4
    wceq
    #
    vx
    con0
    wral
    @11
    vx
    cB
    cA
    noseponlem
    @10
    @28
    vx
    con0
    @4
    @5
    eqcom
    ralbii
    sylnibr
    3expia
    ancoms
    jaod
    syld
    con4d
    3impia
    @0
    @1
    @11
    @19
    @0
    @11
    @19
    wi
    #
    @1
    @0
    @26
    @16
    con0
    wss
    @29
    @27
    @16
    ordsson
    @10
    vx
    @16
    con0
    ssralv
    3syl
    adantr
    3impia
    @15
    cA
    wfun
    #
    cB
    wfun
    #
    @12
    @18
    @19
    wa
    wb
    @0
    @1
    @30
    @11
    cA
    nofun
    3ad2ant1
    @1
    @0
    @31
    @11
    cB
    nofun
    3ad2ant2
    vx
    cA
    cB
    eqfunfv
    syl2anc
    mpbir2and
    3expia
    syl5bi
    necon1ad
    3impia
    @6
    vx
    onintrab2
    sylib
end
