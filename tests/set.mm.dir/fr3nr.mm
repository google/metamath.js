include "wfr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3o.mm"
include "cv.mm"
include "ctp.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "tpex.mm"
include "a1i.mm"
include "simpl.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-tp.mm"
include "simpr1.mm"
include "simpr2.mm"
include "prssi.mm"
include "syl2anc.mm"
include "simpr3.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "tpnzd.mm"
include "fri.mm"
include "syl22anc.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rextpg.mm"
include "adantl.mm"
include "mpbid.mm"
include "wi.mm"
include "snsstp3.mm"
include "snssg.mm"
include "syl.mm"
include "mpbiri.mm"
include "breq1.mm"
include "rspcv.mm"
include "snsstp1.mm"
include "snsstp2.mm"
include "3orim123d.mm"
include "mpd.mm"
include "3ianor.mm"
include "sylibr.mm"
include "3anrot.mm"
include "sylnib.mm"

theorem fr3nr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R Fr A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) )

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
    cD
    cA
    wcel
    #
    w3a
    #
    wa
    #
    cD
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    wbr
    #
    cC
    cD
    cR
    wbr
    #
    w3a
    #
    @7
    @8
    @6
    w3a
    @5
    @6
    wn
    #
    @7
    wn
    #
    @8
    wn
    #
    w3o
    #
    @9
    wn
    @5
    vy
    cv
    #
    cB
    cR
    wbr
    #
    wn
    #
    vy
    cB
    cC
    cD
    ctp
    #
    wral
    #
    @14
    cC
    cR
    wbr
    #
    wn
    #
    vy
    @17
    wral
    #
    @14
    cD
    cR
    wbr
    #
    wn
    #
    vy
    @17
    wral
    #
    w3o
    #
    @13
    @5
    @14
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    @17
    wral
    #
    vx
    @17
    wrex
    #
    @25
    @5
    @17
    cvv
    wcel
    #
    @0
    @17
    cA
    wss
    @17
    c0
    wne
    @30
    @31
    @5
    cB
    cC
    cD
    tpex
    a1i
    @0
    @4
    simpl
    @5
    @17
    cB
    cC
    cpr
    #
    cD
    csn
    #
    cun
    cA
    cB
    cC
    cD
    df-tp
    @5
    @32
    @33
    cA
    @5
    @1
    @2
    @32
    cA
    wss
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    cB
    cC
    cA
    prssi
    syl2anc
    @5
    cD
    cA
    @0
    @1
    @2
    @3
    simpr3
    #
    snssd
    unssd
    syl5eqss
    @5
    cB
    cC
    cD
    cA
    @34
    tpnzd
    vx
    vy
    cA
    @17
    cvv
    cR
    fri
    syl22anc
    @4
    @30
    @25
    wb
    @0
    @29
    @18
    @21
    @24
    vx
    cB
    cC
    cD
    cA
    cA
    cA
    @26
    cB
    wceq
    #
    @28
    @16
    vy
    @17
    @37
    @27
    @15
    @26
    cB
    @14
    cR
    breq2
    notbid
    ralbidv
    @26
    cC
    wceq
    #
    @28
    @20
    vy
    @17
    @38
    @27
    @19
    @26
    cC
    @14
    cR
    breq2
    notbid
    ralbidv
    @26
    cD
    wceq
    #
    @28
    @23
    vy
    @17
    @39
    @27
    @22
    @26
    cD
    @14
    cR
    breq2
    notbid
    ralbidv
    rextpg
    adantl
    mpbid
    @5
    @18
    @10
    @21
    @11
    @24
    @12
    @5
    cD
    @17
    wcel
    #
    @18
    @10
    wi
    @5
    @40
    @33
    @17
    wss
    #
    cB
    cC
    cD
    snsstp3
    @5
    @3
    @40
    @41
    wb
    @36
    cD
    @17
    cA
    snssg
    syl
    mpbiri
    @16
    @10
    vy
    cD
    @17
    @14
    cD
    wceq
    @15
    @6
    @14
    cD
    cB
    cR
    breq1
    notbid
    rspcv
    syl
    @5
    cB
    @17
    wcel
    #
    @21
    @11
    wi
    @5
    @42
    cB
    csn
    @17
    wss
    #
    cB
    cC
    cD
    snsstp1
    @5
    @1
    @42
    @43
    wb
    @34
    cB
    @17
    cA
    snssg
    syl
    mpbiri
    @20
    @11
    vy
    cB
    @17
    @14
    cB
    wceq
    @19
    @7
    @14
    cB
    cC
    cR
    breq1
    notbid
    rspcv
    syl
    @5
    cC
    @17
    wcel
    #
    @24
    @12
    wi
    @5
    @44
    cC
    csn
    @17
    wss
    #
    cB
    cC
    cD
    snsstp2
    @5
    @2
    @44
    @45
    wb
    @35
    cC
    @17
    cA
    snssg
    syl
    mpbiri
    @23
    @12
    vy
    cC
    @17
    @14
    cC
    wceq
    @22
    @8
    @14
    cC
    cD
    cR
    breq1
    notbid
    rspcv
    syl
    3orim123d
    mpd
    @6
    @7
    @8
    3ianor
    sylibr
    @6
    @7
    @8
    3anrot
    sylnib
end
