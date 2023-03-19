include "cpconn.mm"
include "wcel.mm"
include "wa.mm"
include "csconn.mm"
include "cpi1.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "c0g.mm"
include "csn.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cphtpc.mm"
include "cec.mm"
include "cii.mm"
include "ccn.mm"
include "wrex.mm"
include "ctop.mm"
include "wb.mm"
include "sconntop.mm"
include "adantl.mm"
include "simpl.mm"
include "eqid.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "simpr.mm"
include "elpi1.mm"
include "syl2anc.mm"
include "cicc.mm"
include "cxp.mm"
include "wer.mm"
include "phtpcer.mm"
include "a1i.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "eqtr4d.mm"
include "sconnpht.mm"
include "syl3anc.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "breqtrd.mm"
include "erthi.mm"
include "pi1id.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "velsn.mm"
include "eqeq1.mm"
include "syl5bb.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "cgrp.mm"
include "pi1grp.mm"
include "grpidcl.mm"
include "syl.mm"
include "snssd.mm"
include "eqssd.mm"
include "fvex.mm"
include "ensn1.mm"
include "syl6eqbr.mm"
include "adantll.mm"
include "wi.mm"
include "wral.mm"
include "simpll.mm"
include "simplll.mm"
include "pconntop.mm"
include "wf.mm"
include "iiuni.mm"
include "cnf.mm"
include "0elunit.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "eqidd.mm"
include "eqcomd.mm"
include "elpi1i.mm"
include "w3a.mm"
include "pcoptcl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "cgic.mm"
include "pconnpi1.mm"
include "gicen.mm"
include "entr.mm"
include "en1eqsn.mm"
include "eleqtrd.mm"
include "elsni.mm"
include "erth.mm"
include "mpbird.mm"
include "expr.mm"
include "ralrimiva.mm"
include "issconn.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem sconnpi1
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  assume sconnpi1.1: |- X = U. J


  assert |- ( ( J e. PConn /\ Y e. X ) -> ( J e. SConn <-> ( Base ` ( J pi1 Y ) ) ~~ 1o ) )

  proof
    cJ
    cpconn
    wcel
    #
    cY
    cX
    wcel
    #
    wa
    #
    cJ
    csconn
    wcel
    #
    cJ
    cY
    cpi1
    co
    #
    cbs
    cfv
    #
    c1o
    cen
    wbr
    #
    @1
    @3
    @6
    @0
    @1
    @3
    wa
    #
    @5
    @4
    c0g
    cfv
    #
    csn
    #
    c1o
    cen
    @7
    @5
    @9
    @7
    vx
    @5
    @9
    @7
    vx
    cv
    #
    @5
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    cY
    wceq
    #
    c1
    @12
    cfv
    #
    cY
    wceq
    #
    wa
    #
    @10
    @12
    cJ
    cphtpc
    cfv
    #
    cec
    #
    wceq
    #
    wa
    #
    vf
    cii
    cJ
    ccn
    co
    #
    wrex
    #
    @10
    @9
    wcel
    #
    @7
    cJ
    ctop
    wcel
    #
    @1
    @11
    @23
    wb
    @3
    @25
    @1
    cJ
    sconntop
    adantl
    #
    @1
    @3
    simpl
    #
    @25
    @1
    wa
    #
    @5
    vf
    @10
    @4
    cJ
    cX
    cY
    @4
    eqid
    #
    @5
    eqid
    #
    @28
    @25
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @25
    @1
    simpl
    cJ
    cX
    sconnpi1.1
    toptopon
    #
    sylib
    @25
    @1
    simpr
    elpi1
    syl2anc
    @7
    @21
    @24
    vf
    @22
    @7
    @12
    @22
    wcel
    #
    wa
    #
    @17
    @20
    @24
    @34
    @17
    wa
    #
    @24
    @20
    @19
    @8
    wceq
    #
    @35
    @19
    cc0
    c1
    cicc
    co
    #
    cY
    csn
    #
    cxp
    #
    @18
    cec
    #
    @8
    @35
    @12
    @39
    @18
    @22
    @22
    @18
    wer
    #
    @35
    cJ
    phtpcer
    #
    a1i
    @35
    @12
    @37
    @13
    csn
    #
    cxp
    #
    @39
    @18
    @35
    @3
    @33
    @13
    @15
    wceq
    #
    @12
    @44
    @18
    wbr
    #
    @1
    @3
    @33
    @17
    simpllr
    @7
    @33
    @17
    simplr
    @35
    @13
    cY
    @15
    @34
    @14
    @16
    simprl
    #
    @34
    @14
    @16
    simprr
    eqtr4d
    @12
    cJ
    sconnpht
    syl3anc
    @35
    @43
    @38
    @37
    @35
    @13
    cY
    @47
    sneqd
    xpeq2d
    breqtrd
    erthi
    @7
    @40
    @8
    wceq
    #
    @33
    @17
    @7
    @31
    @1
    @48
    @7
    @25
    @31
    @26
    @32
    sylib
    #
    @27
    @4
    cJ
    cX
    cY
    @39
    @29
    @39
    eqid
    pi1id
    syl2anc
    ad2antrr
    eqtrd
    @24
    @10
    @8
    wceq
    @20
    @36
    vx
    @8
    velsn
    @10
    @19
    @8
    eqeq1
    syl5bb
    syl5ibrcom
    expimpd
    rexlimdva
    sylbid
    ssrdv
    @7
    @8
    @5
    @7
    @4
    cgrp
    wcel
    #
    @8
    @5
    wcel
    @7
    @31
    @1
    @50
    @49
    @27
    @4
    cJ
    cX
    cY
    @29
    pi1grp
    syl2anc
    @5
    @4
    @8
    @30
    @8
    eqid
    grpidcl
    syl
    snssd
    eqssd
    @8
    @4
    c0g
    fvex
    ensn1
    syl6eqbr
    adantll
    @2
    @6
    wa
    #
    @0
    @45
    @46
    wi
    #
    vf
    @22
    wral
    @3
    @0
    @1
    @6
    simpll
    @51
    @52
    vf
    @22
    @51
    @33
    @45
    @46
    @51
    @33
    @45
    wa
    #
    wa
    #
    @46
    @19
    @44
    @18
    cec
    #
    wceq
    #
    @54
    @19
    @55
    csn
    #
    wcel
    @56
    @54
    @19
    cJ
    @13
    cpi1
    co
    #
    cbs
    cfv
    #
    @57
    @54
    @59
    @12
    @58
    cJ
    cX
    @13
    @58
    eqid
    #
    @59
    eqid
    #
    @54
    @25
    @31
    @54
    @0
    @25
    @0
    @1
    @6
    @53
    simplll
    #
    cJ
    pconntop
    syl
    @32
    sylib
    #
    @54
    @37
    cX
    @12
    wf
    #
    cc0
    @37
    wcel
    @13
    cX
    wcel
    #
    @54
    @33
    @64
    @51
    @33
    @45
    simprl
    #
    @12
    cii
    cJ
    @37
    cX
    iiuni
    sconnpi1.1
    cnf
    syl
    0elunit
    @37
    cX
    cc0
    @12
    ffvelrn
    sylancl
    #
    @66
    @54
    @13
    eqidd
    @54
    @13
    @15
    @51
    @33
    @45
    simprr
    eqcomd
    elpi1i
    @54
    @55
    @59
    wcel
    @59
    c1o
    cen
    wbr
    #
    @59
    @57
    wceq
    @54
    @59
    @44
    @58
    cJ
    cX
    @13
    @60
    @61
    @63
    @67
    @54
    @44
    @22
    wcel
    #
    cc0
    @44
    cfv
    @13
    wceq
    #
    c1
    @44
    cfv
    @13
    wceq
    #
    @54
    @31
    @65
    @69
    @70
    @71
    w3a
    @63
    @67
    @44
    cJ
    cX
    @13
    @44
    eqid
    pcoptcl
    syl2anc
    #
    simp1d
    @54
    @69
    @70
    @71
    @72
    simp2d
    @54
    @69
    @70
    @71
    @72
    simp3d
    elpi1i
    @54
    @59
    @5
    cen
    wbr
    #
    @6
    @68
    @54
    @58
    @4
    cgic
    wbr
    #
    @73
    @54
    @0
    @65
    @1
    @74
    @62
    @67
    @0
    @1
    @6
    @53
    simpllr
    @13
    cY
    @58
    @4
    @59
    @5
    cJ
    cX
    sconnpi1.1
    @60
    @29
    @61
    @30
    pconnpi1
    syl3anc
    @59
    @5
    @58
    @4
    @61
    @30
    gicen
    syl
    @2
    @6
    @53
    simplr
    @59
    @5
    c1o
    entr
    syl2anc
    @55
    @59
    en1eqsn
    syl2anc
    eleqtrd
    @19
    @55
    elsni
    syl
    @54
    @12
    @44
    @18
    @22
    @41
    @54
    @42
    a1i
    @66
    erth
    mpbird
    expr
    ralrimiva
    vf
    cJ
    issconn
    sylanbrc
    impbida
end
