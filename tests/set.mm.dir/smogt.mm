include "wfn.mm"
include "wsmo.mm"
include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "imbi2d.mm"
include "con0.mm"
include "w3a.mm"
include "word.mm"
include "smodm2.mm"
include "3adant3.mm"
include "simp3.mm"
include "ordelord.mm"
include "syl2anc.mm"
include "vex.mm"
include "elon.mm"
include "sylibr.mm"
include "weq.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "imbi12d.mm"
include "wral.mm"
include "wel.mm"
include "simpl1.mm"
include "simpl2.mm"
include "ordtr1.mm"
include "expcomd.mm"
include "sylc.mm"
include "imp.mm"
include "pm2.27.mm"
include "syl3anc.mm"
include "ralimdva.mm"
include "simp31.mm"
include "simp32.mm"
include "smofvon2.mm"
include "3ad2ant2.mm"
include "eloni.mm"
include "syl.mm"
include "simp33.mm"
include "smoel2.mm"
include "3adantr3.mm"
include "3impa.mm"
include "ordtr2.mm"
include "syl22anc.mm"
include "3expia.mm"
include "3expd.mm"
include "3impia.mm"
include "dfss3.mm"
include "syl6ibr.mm"
include "syldc.mm"
include "a1i.mm"
include "tfis2.mm"
include "mpcom.mm"
include "com12.mm"
include "vtoclga.mm"

theorem smogt
  let cA: class A
  let cC: class C
  let cF: class F
  let vy: setvar y
  let vx: setvar x


  assert |- ( ( F Fn A /\ Smo F /\ C e. A ) -> C C_ ( F ` C ) )

  proof
    cF
    cA
    wfn
    #
    cF
    wsmo
    #
    cC
    cA
    wcel
    #
    cC
    cC
    cF
    cfv
    #
    wss
    #
    @2
    @0
    @1
    wa
    #
    @4
    @5
    vx
    cv
    #
    @6
    cF
    cfv
    #
    wss
    #
    wi
    @5
    @4
    wi
    vx
    cC
    cA
    @6
    cC
    wceq
    #
    @8
    @4
    @5
    @9
    @6
    cC
    @7
    @3
    @9
    id
    @6
    cC
    cF
    fveq2
    sseq12d
    imbi2d
    @5
    @6
    cA
    wcel
    #
    @8
    @0
    @1
    @10
    @8
    @6
    con0
    wcel
    #
    @0
    @1
    @10
    w3a
    #
    @8
    @12
    @6
    word
    #
    @11
    @12
    cA
    word
    #
    @10
    @13
    @0
    @1
    @14
    @10
    cA
    cF
    smodm2
    #
    3adant3
    #
    @0
    @1
    @10
    simp3
    #
    cA
    @6
    ordelord
    #
    syl2anc
    @6
    vx
    vex
    elon
    sylibr
    @12
    @8
    wi
    #
    @0
    @1
    vy
    cv
    #
    cA
    wcel
    #
    w3a
    #
    @20
    @20
    cF
    cfv
    #
    wss
    #
    wi
    #
    vx
    vy
    vx
    vy
    weq
    #
    @12
    @22
    @8
    @24
    @26
    @10
    @21
    @0
    @1
    @6
    @20
    cA
    eleq1
    3anbi3d
    @26
    @6
    @20
    @7
    @23
    @26
    id
    @6
    @20
    cF
    fveq2
    sseq12d
    imbi12d
    @25
    vy
    @6
    wral
    #
    @19
    wi
    @11
    @12
    @27
    @24
    vy
    @6
    wral
    #
    @8
    @12
    @25
    @24
    vy
    @6
    @12
    vy
    vx
    wel
    #
    wa
    @0
    @1
    @21
    @25
    @24
    wi
    @0
    @1
    @10
    @29
    simpl1
    @0
    @1
    @10
    @29
    simpl2
    @12
    @29
    @21
    @12
    @14
    @10
    @29
    @21
    wi
    @16
    @17
    @14
    @29
    @10
    @21
    @20
    @6
    cA
    ordtr1
    expcomd
    sylc
    imp
    @22
    @24
    pm2.27
    syl3anc
    ralimdva
    @12
    @28
    @20
    @7
    wcel
    #
    vy
    @6
    wral
    @8
    @12
    @24
    @30
    vy
    @6
    @12
    @29
    @24
    @30
    wi
    #
    @0
    @1
    @10
    @29
    @31
    wi
    @5
    @10
    @29
    @24
    @30
    @0
    @1
    @10
    @29
    @24
    w3a
    #
    @30
    @0
    @1
    @32
    w3a
    #
    @20
    word
    #
    @7
    word
    #
    @24
    @23
    @7
    wcel
    #
    @30
    @33
    @13
    @29
    @34
    @33
    @14
    @10
    @13
    @0
    @1
    @14
    @32
    @15
    3adant3
    @0
    @1
    @10
    @29
    @24
    simp31
    @18
    syl2anc
    @0
    @1
    @10
    @29
    @24
    simp32
    @6
    @20
    ordelord
    syl2anc
    @33
    @7
    con0
    wcel
    #
    @35
    @1
    @0
    @37
    @32
    @6
    cF
    smofvon2
    3ad2ant2
    @7
    eloni
    syl
    @0
    @1
    @10
    @29
    @24
    simp33
    @0
    @1
    @32
    @36
    @5
    @10
    @29
    @36
    @24
    cA
    @6
    @20
    cF
    smoel2
    3adantr3
    3impa
    @34
    @35
    wa
    @24
    @36
    wa
    @30
    @20
    @23
    @7
    ordtr2
    imp
    syl22anc
    3expia
    3expd
    3impia
    imp
    ralimdva
    vy
    @6
    @7
    dfss3
    syl6ibr
    syldc
    a1i
    tfis2
    mpcom
    3expia
    com12
    vtoclga
    com12
    3impia
end
