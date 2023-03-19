include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cint.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cdif.mm"
include "cfn.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "elpwi.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "wb.mm"
include "ufilb.mm"
include "adantr.mm"
include "cfil.mm"
include "ufilfil.mm"
include "filfinnfr.mm"
include "3exp.mm"
include "com23.mm"
include "syl.mm"
include "imp.mm"
include "sylbid.mm"
include "necon4bd.mm"
include "ex.mm"
include "sylan2.mm"
include "ralrimdva.mm"
include "csn.mm"
include "uffixsn.mm"
include "filelss.mm"
include "syl2anc.mm"
include "dfss4.mm"
include "sylib.mm"
include "snfi.mm"
include "syl6eqel.mm"
include "difss.mm"
include "filtop.mm"
include "elpw2g.mm"
include "3syl.mm"
include "mpbiri.mm"
include "difeq2.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "syldan.mm"
include "pm2.24d.mm"
include "sylbird.mm"
include "syld.mm"
include "impancom.mm"
include "pm2.01d.mm"
include "eq0rdv.mm"
include "impbid.mm"
include "rabss.mm"
include "syl6bbr.mm"

theorem cfinufil
  let vx: setvar x
  let cF: class F
  let cX: class X
  let cA: class A
  let vy: setvar y

  disjoint F x
  disjoint X x
  disjoint A x
  disjoint x y
  disjoint F y
  disjoint X y
  assert |- ( F e. ( UFil ` X ) -> ( |^| F = (/) <-> { x e. ~P X | ( X \ x ) e. Fin } C_ F ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cF
    cint
    #
    c0
    wceq
    #
    cX
    vx
    cv
    #
    cdif
    #
    cfn
    wcel
    #
    @3
    cF
    wcel
    #
    wi
    #
    vx
    cX
    cpw
    #
    wral
    #
    @5
    vx
    @8
    crab
    cF
    wss
    @0
    @2
    @9
    @0
    @2
    @7
    vx
    @8
    @3
    @8
    wcel
    @0
    @3
    cX
    wss
    #
    @2
    @7
    wi
    @3
    cX
    elpwi
    @0
    @10
    wa
    #
    @5
    @2
    @6
    @11
    @5
    @2
    @6
    wi
    @11
    @5
    wa
    #
    @6
    @1
    c0
    @12
    @6
    wn
    #
    @4
    cF
    wcel
    #
    @1
    c0
    wne
    #
    @11
    @13
    @14
    wb
    @5
    @3
    cF
    cX
    ufilb
    adantr
    @11
    @5
    @14
    @15
    wi
    #
    @11
    cF
    cX
    cfil
    cfv
    wcel
    #
    @5
    @16
    wi
    @0
    @17
    @10
    cF
    cX
    ufilfil
    #
    adantr
    @17
    @14
    @5
    @15
    @17
    @14
    @5
    @15
    @4
    cF
    cX
    filfinnfr
    3exp
    com23
    syl
    imp
    sylbid
    necon4bd
    ex
    com23
    sylan2
    ralrimdva
    @0
    @9
    @2
    @0
    @9
    wa
    #
    vy
    @1
    @19
    vy
    cv
    #
    @1
    wcel
    #
    @0
    @21
    @9
    @21
    wn
    #
    @0
    @21
    wa
    #
    @9
    cX
    @20
    csn
    #
    cdif
    #
    cF
    wcel
    #
    @22
    @23
    @9
    cX
    @25
    cdif
    #
    cfn
    wcel
    #
    @26
    @23
    @27
    @24
    cfn
    @23
    @24
    cX
    wss
    #
    @27
    @24
    wceq
    @23
    @17
    @24
    cF
    wcel
    #
    @29
    @0
    @17
    @21
    @18
    adantr
    #
    @20
    cF
    cX
    uffixsn
    #
    @24
    cF
    cX
    filelss
    syl2anc
    #
    @24
    cX
    dfss4
    sylib
    @20
    snfi
    syl6eqel
    @23
    @25
    @8
    wcel
    #
    @9
    @28
    @26
    wi
    #
    wi
    @23
    @34
    @25
    cX
    wss
    #
    cX
    @24
    difss
    @23
    @17
    cX
    cF
    wcel
    @34
    @36
    wb
    @31
    cF
    cX
    filtop
    @25
    cX
    cF
    elpw2g
    3syl
    mpbiri
    @7
    @35
    vx
    @25
    @8
    @3
    @25
    wceq
    #
    @5
    @28
    @6
    @26
    @37
    @4
    @27
    cfn
    @3
    @25
    cX
    difeq2
    eleq1d
    @3
    @25
    cF
    eleq1
    imbi12d
    rspcv
    syl
    mpid
    @23
    @26
    @30
    wn
    #
    @22
    @0
    @21
    @29
    @38
    @26
    wb
    @33
    @24
    cF
    cX
    ufilb
    syldan
    @23
    @30
    @22
    @32
    pm2.24d
    sylbird
    syld
    impancom
    pm2.01d
    eq0rdv
    ex
    impbid
    @5
    vx
    @8
    cF
    rabss
    syl6bbr
end
