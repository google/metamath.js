include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cen.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "ciun.mm"
include "crn.mm"
include "cmpt.mm"
include "wfo.mm"
include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "infxpidm2.mm"
include "infn0.mm"
include "adantl.mm"
include "fseqen.mm"
include "syl2anc.mm"
include "xpdom1g.mm"
include "domentr.mm"
include "endomtr.mm"
include "numdom.mm"
include "syldan.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "wrex.mm"
include "eliun.mm"
include "wss.mm"
include "elmapi.mm"
include "ad2antll.mm"
include "frn.mm"
include "syl.mm"
include "vex.mm"
include "rnex.mm"
include "elpw.mm"
include "sylibr.mm"
include "simprl.mm"
include "ssid.mm"
include "ssnnfi.mm"
include "sylancl.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "elind.mm"
include "expr.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "imp.mm"
include "eqid.mm"
include "fmptd.mm"
include "wex.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "isfi.mm"
include "wf1o.mm"
include "ensym.mm"
include "bren.mm"
include "f1of.mm"
include "inss1.mm"
include "simplr.mm"
include "elpwid.mm"
include "fssd.mm"
include "cvv.mm"
include "wb.mm"
include "simplll.mm"
include "elmapg.mm"
include "mpbird.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "f1ofo.mm"
include "forn.mm"
include "eqcomd.mm"
include "jca.mm"
include "eximdv.mm"
include "syl5.mm"
include "mpd.mm"
include "ex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "df-rex.mm"
include "bitri.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "fodomnum.mm"
include "sylc.mm"
include "domtr.mm"
include "pwexg.mm"
include "adantr.mm"
include "inex1g.mm"
include "infpwfidom.mm"
include "sbth.mm"

theorem infpwfien
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. dom card /\ _om ~<_ A ) -> ( ~P A i^i Fin ) ~~ A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    wa
    #
    cA
    cpw
    #
    cfn
    cin
    #
    cA
    cdom
    wbr
    #
    cA
    @5
    cdom
    wbr
    #
    @5
    cA
    cen
    wbr
    @3
    @5
    vn
    com
    cA
    vn
    cv
    #
    cmap
    co
    #
    ciun
    #
    cdom
    wbr
    #
    @10
    cA
    cdom
    wbr
    #
    @6
    @3
    @10
    @0
    wcel
    #
    @10
    @5
    vx
    @10
    vx
    cv
    #
    crn
    #
    cmpt
    #
    wfo
    #
    @11
    @1
    @2
    @12
    @13
    @3
    @10
    com
    cA
    cxp
    #
    cen
    wbr
    #
    @18
    cA
    cdom
    wbr
    #
    @12
    @3
    cA
    cA
    cxp
    #
    cA
    cen
    wbr
    #
    cA
    c0
    wne
    #
    @19
    cA
    infxpidm2
    #
    @2
    @23
    @1
    cA
    infn0
    adantl
    cA
    vn
    fseqen
    syl2anc
    @3
    @18
    @21
    cdom
    wbr
    @22
    @20
    com
    cA
    cA
    @0
    xpdom1g
    @24
    @18
    @21
    cA
    domentr
    syl2anc
    @10
    @18
    cA
    endomtr
    syl2anc
    #
    cA
    @10
    numdom
    syldan
    @3
    @16
    @10
    wfn
    #
    @16
    crn
    #
    @5
    wceq
    @17
    @3
    @10
    @5
    @16
    wf
    #
    @26
    @3
    vx
    @10
    @15
    @5
    @16
    @3
    @14
    @10
    wcel
    #
    @15
    @5
    wcel
    #
    @29
    @14
    @9
    wcel
    #
    vn
    com
    wrex
    #
    @3
    @30
    vn
    @14
    com
    @9
    eliun
    #
    @3
    @31
    @30
    vn
    com
    @3
    @8
    com
    wcel
    #
    @31
    @30
    @3
    @34
    @31
    wa
    wa
    #
    @4
    cfn
    @15
    @35
    @15
    cA
    wss
    #
    @15
    @4
    wcel
    @35
    @8
    cA
    @14
    wf
    #
    @36
    @31
    @37
    @3
    @34
    @14
    cA
    @8
    elmapi
    ad2antll
    #
    @8
    cA
    @14
    frn
    syl
    @15
    cA
    @14
    vx
    vex
    rnex
    elpw
    sylibr
    @35
    @8
    cfn
    wcel
    #
    @8
    @15
    @14
    wfo
    #
    @15
    cfn
    wcel
    @35
    @34
    @8
    @8
    wss
    @39
    @3
    @34
    @31
    simprl
    @8
    ssid
    @8
    @8
    ssnnfi
    sylancl
    @35
    @37
    @40
    @38
    @37
    @14
    @8
    wfn
    @40
    @8
    cA
    @14
    ffn
    @8
    @14
    dffn4
    sylib
    syl
    @8
    @15
    @14
    fofi
    syl2anc
    elind
    expr
    rexlimdva
    syl5bi
    imp
    @16
    eqid
    #
    fmptd
    #
    @10
    @5
    @16
    ffn
    syl
    @3
    @27
    @5
    @3
    @28
    @27
    @5
    wss
    @42
    @10
    @5
    @16
    frn
    syl
    @3
    vy
    @5
    @27
    @3
    vy
    cv
    #
    @5
    wcel
    #
    @29
    @43
    @15
    wceq
    #
    wa
    #
    vx
    wex
    #
    @43
    @27
    wcel
    #
    @3
    @44
    @47
    @3
    @44
    wa
    #
    @43
    vm
    cv
    #
    cen
    wbr
    #
    vm
    com
    wrex
    #
    @47
    @49
    @43
    cfn
    wcel
    @52
    @49
    @5
    cfn
    @43
    @4
    cfn
    inss2
    @3
    @44
    simpr
    sseldi
    vm
    @43
    isfi
    sylib
    @49
    @51
    @47
    vm
    com
    @51
    @50
    @43
    @14
    wf1o
    #
    vx
    wex
    #
    @49
    @50
    com
    wcel
    #
    wa
    #
    @47
    @51
    @50
    @43
    cen
    wbr
    @54
    @43
    @50
    ensym
    @50
    @43
    vx
    bren
    sylib
    @56
    @53
    @46
    vx
    @49
    @55
    @53
    @46
    @49
    @55
    @53
    wa
    #
    wa
    #
    @29
    @45
    @58
    @32
    @29
    @58
    @55
    @14
    cA
    @50
    cmap
    co
    #
    wcel
    #
    @32
    @49
    @55
    @53
    simprl
    @58
    @60
    @50
    cA
    @14
    wf
    #
    @58
    @50
    @43
    cA
    @14
    @53
    @50
    @43
    @14
    wf
    @49
    @55
    @50
    @43
    @14
    f1of
    ad2antll
    @58
    @43
    cA
    @58
    @5
    @4
    @43
    @4
    cfn
    inss1
    @3
    @44
    @57
    simplr
    sseldi
    elpwid
    fssd
    @58
    @1
    @50
    cvv
    wcel
    @60
    @61
    wb
    @1
    @2
    @44
    @57
    simplll
    vm
    vex
    cA
    @50
    @14
    @0
    cvv
    elmapg
    sylancl
    mpbird
    @31
    @60
    vn
    @50
    com
    @8
    @50
    wceq
    @9
    @59
    @14
    @8
    @50
    cA
    cmap
    oveq2
    eleq2d
    rspcev
    syl2anc
    @33
    sylibr
    @58
    @15
    @43
    @58
    @50
    @43
    @14
    wfo
    #
    @15
    @43
    wceq
    @53
    @62
    @49
    @55
    @50
    @43
    @14
    f1ofo
    ad2antll
    @50
    @43
    @14
    forn
    syl
    eqcomd
    jca
    expr
    eximdv
    syl5
    rexlimdva
    mpd
    ex
    @48
    @45
    vx
    @10
    wrex
    #
    @47
    @43
    cvv
    wcel
    @48
    @63
    wb
    vy
    vex
    vx
    @10
    @15
    @43
    @16
    cvv
    @41
    elrnmpt
    ax-mp
    @45
    vx
    @10
    df-rex
    bitri
    syl6ibr
    ssrdv
    eqssd
    @10
    @5
    @16
    df-fo
    sylanbrc
    @10
    @5
    @16
    fodomnum
    sylc
    @25
    @5
    @10
    cA
    domtr
    syl2anc
    @3
    @5
    cvv
    wcel
    #
    @7
    @3
    @4
    cvv
    wcel
    #
    @64
    @1
    @65
    @2
    cA
    @0
    pwexg
    adantr
    @4
    cfn
    cvv
    inex1g
    syl
    cA
    infpwfidom
    syl
    @5
    cA
    sbth
    syl2anc
end
