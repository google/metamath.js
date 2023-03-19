include "wcel.mm"
include "cfn.mm"
include "cpw.mm"
include "crpss.mm"
include "ccnv.mm"
include "wfr.mm"
include "wpo.mm"
include "porpss.mm"
include "cnvpo.mm"
include "mpbi.mm"
include "pwfi.mm"
include "biimpi.mm"
include "frfi.mm"
include "sylancr.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "wss.mm"
include "inss2.mm"
include "pwexg.mm"
include "ssexg.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "0fin.mm"
include "0elpw.mm"
include "elin.mm"
include "mpbir2an.mm"
include "ne0ii.mm"
include "fri.mm"
include "mpanr12.mm"
include "sylan.mm"
include "ex.mm"
include "inss1.mm"
include "simpl.mm"
include "sseldi.mm"
include "ralnex.mm"
include "csn.mm"
include "cun.mm"
include "sseli.mm"
include "adantr.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "simprbi.mm"
include "elpwid.mm"
include "snssi.mm"
include "ad2antrl.mm"
include "unssd.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "elpw.mm"
include "sylibr.mm"
include "elind.mm"
include "wpss.mm"
include "wceq.mm"
include "disjsn.mm"
include "biimpri.mm"
include "snnz.mm"
include "disjpss.mm"
include "ad2antll.mm"
include "brcnv.mm"
include "brrpss.mm"
include "bitri.mm"
include "breq1.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "expr.mm"
include "con1d.mm"
include "syl5bi.mm"
include "impancom.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "rexlimiva.mm"
include "syl6.mm"
include "impbid2.mm"

theorem isfin1-3
  let cA: class A
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. V -> ( A e. Fin <-> `' [C.] Fr ~P A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    #
    cA
    cpw
    #
    crpss
    ccnv
    #
    wfr
    #
    @1
    @2
    @3
    wpo
    #
    @2
    cfn
    wcel
    #
    @4
    @2
    crpss
    wpo
    @5
    @2
    porpss
    @2
    crpss
    cnvpo
    mpbi
    @1
    @6
    cA
    pwfi
    biimpi
    @2
    @3
    frfi
    sylancr
    @0
    @4
    vc
    cv
    #
    vb
    cv
    #
    @3
    wbr
    #
    wn
    vc
    cfn
    @2
    cin
    #
    wral
    #
    vb
    @10
    wrex
    #
    @1
    @0
    @4
    @12
    @0
    @10
    cvv
    wcel
    #
    @4
    @12
    @0
    @10
    @2
    wss
    #
    @2
    cvv
    wcel
    @13
    cfn
    @2
    inss2
    #
    cA
    cV
    pwexg
    @10
    @2
    cvv
    ssexg
    sylancr
    @13
    @4
    wa
    @14
    @10
    c0
    wne
    @12
    @15
    c0
    @10
    c0
    @10
    wcel
    c0
    cfn
    wcel
    c0
    @2
    wcel
    0fin
    cA
    0elpw
    c0
    cfn
    @2
    elin
    mpbir2an
    ne0ii
    vb
    vc
    @2
    @10
    cvv
    @3
    fri
    mpanr12
    sylan
    ex
    @11
    @1
    vb
    @10
    @8
    @10
    wcel
    #
    @11
    wa
    #
    @8
    cfn
    wcel
    #
    cA
    @8
    wss
    @1
    @17
    @10
    cfn
    @8
    cfn
    @2
    inss1
    #
    @16
    @11
    simpl
    sseldi
    @17
    vd
    cA
    @8
    @16
    vd
    cv
    #
    cA
    wcel
    #
    @11
    @20
    @8
    wcel
    #
    @11
    @9
    vc
    @10
    wrex
    #
    wn
    @16
    @21
    wa
    #
    @22
    @9
    vc
    @10
    ralnex
    @24
    @22
    @23
    @16
    @21
    @22
    wn
    #
    @23
    @16
    @21
    @25
    wa
    #
    wa
    #
    @8
    @20
    csn
    #
    cun
    #
    @10
    wcel
    @29
    @8
    @3
    wbr
    #
    @23
    @27
    cfn
    @2
    @29
    @27
    @18
    @28
    cfn
    wcel
    @29
    cfn
    wcel
    @16
    @18
    @26
    @10
    cfn
    @8
    @19
    sseli
    adantr
    @20
    snfi
    @8
    @28
    unfi
    sylancl
    @27
    @29
    cA
    wss
    @29
    @2
    wcel
    @27
    @8
    @28
    cA
    @16
    @8
    cA
    wss
    @26
    @16
    @8
    cA
    @16
    @18
    @8
    @2
    wcel
    @8
    cfn
    @2
    elin
    simprbi
    elpwid
    adantr
    @21
    @28
    cA
    wss
    @16
    @25
    @20
    cA
    snssi
    ad2antrl
    unssd
    @29
    cA
    @8
    @28
    vb
    vex
    #
    @20
    snex
    unex
    #
    elpw
    sylibr
    elind
    @27
    @8
    @29
    wpss
    #
    @30
    @25
    @33
    @16
    @21
    @25
    @8
    @28
    cin
    c0
    wceq
    #
    @28
    c0
    wne
    @33
    @34
    @25
    @8
    @20
    disjsn
    biimpri
    @20
    vd
    vex
    snnz
    @8
    @28
    disjpss
    sylancl
    ad2antll
    @30
    @8
    @29
    crpss
    wbr
    @33
    @29
    @8
    crpss
    @32
    @31
    brcnv
    @8
    @29
    @32
    brrpss
    bitri
    sylibr
    @9
    @30
    vc
    @29
    @10
    @7
    @29
    @8
    @3
    breq1
    rspcev
    syl2anc
    expr
    con1d
    syl5bi
    impancom
    ssrdv
    @8
    cA
    ssfi
    syl2anc
    rexlimiva
    syl6
    impbid2
end
