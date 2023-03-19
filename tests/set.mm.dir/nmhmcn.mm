include "cnlm.mm"
include "cclm.mm"
include "cin.mm"
include "wcel.mm"
include "cq.mm"
include "wss.mm"
include "w3a.mm"
include "cnmhm.mm"
include "co.mm"
include "clmhm.mm"
include "cnghm.mm"
include "wa.mm"
include "ccn.mm"
include "wb.mm"
include "inss1.mm"
include "sseli.mm"
include "isnmhm.mm"
include "baib.mm"
include "syl2an.mm"
include "3adant3.mm"
include "nghmcn.mm"
include "c0g.mm"
include "cfv.mm"
include "cv.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cbl.mm"
include "ccnv.mm"
include "c1.mm"
include "cima.mm"
include "crp.mm"
include "wrex.mm"
include "cxmt.mm"
include "cmopn.mm"
include "cmt.mm"
include "cxme.mm"
include "cngp.mm"
include "simpll1.mm"
include "sseldi.mm"
include "nlmngp.mm"
include "ngpms.mm"
include "3syl.mm"
include "msxms.mm"
include "eqid.mm"
include "xmsxmet.mm"
include "simpr.mm"
include "cxr.mm"
include "simpll2.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "lmod0vcl.mm"
include "1rp.mm"
include "rpxr.mm"
include "mp1i.mm"
include "blopn.mm"
include "syl3anc.mm"
include "wceq.mm"
include "mstopn.mm"
include "4syl.mm"
include "eleqtrrd.mm"
include "cnima.mm"
include "syl2anc.mm"
include "eleqtrd.mm"
include "cghm.mm"
include "lmghm.mm"
include "ad2antlr.mm"
include "ghmid.mm"
include "syl.mm"
include "a1i.mm"
include "blcntr.mm"
include "eqeltrd.mm"
include "wf.mm"
include "wfn.mm"
include "lmhmf.mm"
include "ffn.mm"
include "elpreima.mm"
include "mpbir2and.mm"
include "mopni2.mm"
include "cnmo.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cnm.mm"
include "cgrp.mm"
include "simpl1.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "ngpgrp.mm"
include "nmval2.mm"
include "xmetsym.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "biimpd.mm"
include "elbl.mm"
include "cr.mm"
include "simpl2.mm"
include "simplr.mm"
include "ffvelrnda.mm"
include "nmcl.mm"
include "1re.mm"
include "ltle.mm"
include "sylancl.mm"
include "1red.mm"
include "lediv1d.mm"
include "3imtr3d.mm"
include "adantld.mm"
include "sylbid.mm"
include "imim12d.mm"
include "ralimdva.mm"
include "crab.mm"
include "adantl.mm"
include "blval.mm"
include "sseq1d.mm"
include "rabss.mm"
include "syl6bb.mm"
include "rpreccl.mm"
include "rpxrd.mm"
include "simpl3.mm"
include "nmoleub2b.mm"
include "3imtr4d.mm"
include "3jca.mm"
include "rpred.mm"
include "bddnghm.mm"
include "expr.mm"
include "syld.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "impbid2.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem nmhmcn
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  assume nmhmcn.j: |- J = ( TopOpen ` S )
  assume nmhmcn.k: |- K = ( TopOpen ` T )
  assume nmhmcn.g: |- G = ( Scalar ` S )
  assume nmhmcn.b: |- B = ( Base ` G )


  assert |- ( ( S e. ( NrmMod i^i CMod ) /\ T e. ( NrmMod i^i CMod ) /\ QQ C_ B ) -> ( F e. ( S NMHom T ) <-> ( F e. ( S LMHom T ) /\ F e. ( J Cn K ) ) ) )

  proof
    cS
    cnlm
    cclm
    cin
    #
    wcel
    #
    cT
    @0
    wcel
    #
    cq
    cB
    wss
    #
    w3a
    #
    cF
    cS
    cT
    cnmhm
    co
    wcel
    #
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    wa
    #
    @6
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    wa
    @1
    @2
    @5
    @8
    wb
    #
    @3
    @1
    cS
    cnlm
    wcel
    #
    cT
    cnlm
    wcel
    #
    @10
    @2
    @0
    cnlm
    cS
    cnlm
    cclm
    inss1
    #
    sseli
    @0
    cnlm
    cT
    @13
    sseli
    @5
    @11
    @12
    wa
    @8
    cS
    cT
    cF
    isnmhm
    baib
    syl2an
    3adant3
    @4
    @6
    @7
    @9
    @4
    @6
    wa
    #
    @7
    @9
    cS
    cT
    cF
    cJ
    cK
    nmhmcn.j
    nmhmcn.k
    nghmcn
    @14
    @9
    @7
    @14
    @9
    wa
    #
    cS
    c0g
    cfv
    #
    vx
    cv
    #
    cS
    cds
    cfv
    #
    cS
    cbs
    cfv
    #
    @19
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    cF
    ccnv
    cT
    c0g
    cfv
    #
    c1
    cT
    cds
    cfv
    #
    cT
    cbs
    cfv
    #
    @24
    cxp
    cres
    #
    cbl
    cfv
    co
    #
    cima
    #
    wss
    #
    vx
    crp
    wrex
    #
    @7
    @15
    @20
    @19
    cxmt
    cfv
    wcel
    #
    @27
    @20
    cmopn
    cfv
    #
    wcel
    @16
    @27
    wcel
    #
    @29
    @15
    cS
    cmt
    wcel
    #
    cS
    cxme
    wcel
    @30
    @15
    @11
    cS
    cngp
    wcel
    #
    @33
    @15
    @0
    cnlm
    cS
    @13
    @1
    @2
    @3
    @6
    @9
    simpll1
    #
    sseldi
    #
    cS
    nlmngp
    #
    cS
    ngpms
    #
    3syl
    cS
    msxms
    @20
    cS
    @19
    @19
    eqid
    #
    @20
    eqid
    #
    xmsxmet
    3syl
    #
    @15
    @27
    cJ
    @31
    @15
    @9
    @26
    cK
    wcel
    @27
    cJ
    wcel
    @14
    @9
    simpr
    @15
    @26
    @25
    cmopn
    cfv
    #
    cK
    @15
    @25
    @24
    cxmt
    cfv
    wcel
    #
    @22
    @24
    wcel
    #
    c1
    cxr
    wcel
    #
    @26
    @42
    wcel
    @15
    cT
    cmt
    wcel
    #
    cT
    cxme
    wcel
    @43
    @15
    @12
    cT
    cngp
    wcel
    #
    @46
    @15
    @0
    cnlm
    cT
    @13
    @1
    @2
    @3
    @6
    @9
    simpll2
    #
    sseldi
    #
    cT
    nlmngp
    #
    cT
    ngpms
    #
    3syl
    cT
    msxms
    @25
    cT
    @24
    @24
    eqid
    #
    @25
    eqid
    #
    xmsxmet
    3syl
    #
    @15
    @12
    cT
    clmod
    wcel
    @44
    @49
    cT
    nlmlmod
    @24
    cT
    @22
    @52
    @22
    eqid
    #
    lmod0vcl
    3syl
    #
    c1
    crp
    wcel
    #
    @45
    @15
    1rp
    c1
    rpxr
    #
    mp1i
    @25
    @22
    c1
    @42
    @24
    @42
    eqid
    blopn
    syl3anc
    @15
    @12
    @47
    @46
    cK
    @42
    wceq
    @49
    @50
    @51
    @25
    cK
    cT
    @24
    nmhmcn.k
    @52
    @53
    mstopn
    4syl
    eleqtrrd
    @26
    cF
    cJ
    cK
    cnima
    syl2anc
    @15
    @11
    @34
    @33
    cJ
    @31
    wceq
    @36
    @37
    @38
    @20
    cJ
    cS
    @19
    nmhmcn.j
    @39
    @40
    mstopn
    4syl
    eleqtrd
    @15
    @32
    @16
    @19
    wcel
    #
    @16
    cF
    cfv
    #
    @26
    wcel
    #
    @15
    @11
    cS
    clmod
    wcel
    @59
    @36
    cS
    nlmlmod
    @19
    cS
    @16
    @39
    @16
    eqid
    #
    lmod0vcl
    3syl
    #
    @15
    @60
    @22
    @26
    @15
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @60
    @22
    wceq
    @6
    @64
    @4
    @9
    cS
    cT
    cF
    lmghm
    ad2antlr
    #
    cS
    cT
    cF
    @16
    @22
    @62
    @55
    ghmid
    syl
    @15
    @43
    @44
    @57
    @22
    @26
    wcel
    @54
    @56
    @57
    @15
    1rp
    a1i
    @25
    @22
    c1
    @24
    blcntr
    syl3anc
    eqeltrd
    @15
    @19
    @24
    cF
    wf
    #
    cF
    @19
    wfn
    #
    @32
    @59
    @61
    wa
    wb
    @6
    @66
    @4
    @9
    @19
    @24
    cS
    cT
    cF
    @39
    @52
    lmhmf
    #
    ad2antlr
    #
    @19
    @24
    cF
    ffn
    #
    @19
    @16
    @26
    cF
    elpreima
    3syl
    mpbir2and
    vx
    @27
    @20
    @16
    @31
    @19
    @31
    eqid
    mopni2
    syl3anc
    @15
    @28
    @7
    vx
    crp
    @15
    @17
    crp
    wcel
    #
    wa
    #
    @28
    cF
    cS
    cT
    cnmo
    co
    #
    cfv
    c1
    @17
    cdiv
    co
    #
    cle
    wbr
    #
    @7
    @72
    @16
    vy
    cv
    #
    @20
    co
    #
    @17
    clt
    wbr
    #
    @76
    @27
    wcel
    #
    wi
    #
    vy
    @19
    wral
    #
    @76
    cS
    cnm
    cfv
    #
    cfv
    #
    @17
    clt
    wbr
    #
    @76
    cF
    cfv
    #
    cT
    cnm
    cfv
    #
    cfv
    #
    @17
    cdiv
    co
    @74
    cle
    wbr
    #
    wi
    #
    vy
    @19
    wral
    @28
    @75
    @72
    @80
    @89
    vy
    @19
    @72
    @76
    @19
    wcel
    #
    wa
    #
    @84
    @78
    @79
    @88
    @91
    @84
    @78
    @91
    @83
    @77
    @17
    clt
    @91
    @83
    @76
    @16
    @20
    co
    #
    @77
    @91
    cS
    cgrp
    wcel
    #
    @90
    @83
    @92
    wceq
    @91
    @34
    @93
    @15
    @34
    @71
    @90
    @14
    @34
    @9
    @14
    @11
    @34
    @14
    @0
    cnlm
    cS
    @13
    @1
    @2
    @3
    @6
    simpl1
    sseldi
    @37
    syl
    adantr
    #
    ad2antrr
    cS
    ngpgrp
    syl
    @72
    @90
    simpr
    #
    @76
    @18
    @20
    @82
    cS
    @19
    @16
    @82
    eqid
    #
    @39
    @62
    @18
    eqid
    @40
    nmval2
    syl2anc
    @91
    @30
    @90
    @59
    @92
    @77
    wceq
    @15
    @30
    @71
    @90
    @41
    ad2antrr
    @95
    @15
    @59
    @71
    @90
    @63
    ad2antrr
    @76
    @16
    @20
    @19
    xmetsym
    syl3anc
    eqtrd
    breq1d
    biimpd
    @91
    @79
    @90
    @85
    @26
    wcel
    #
    wa
    #
    @88
    @91
    @66
    @67
    @79
    @98
    wb
    @15
    @66
    @71
    @90
    @69
    ad2antrr
    @70
    @19
    @76
    @26
    cF
    elpreima
    3syl
    @91
    @97
    @88
    @90
    @91
    @97
    @85
    @24
    wcel
    #
    @22
    @85
    @25
    co
    #
    c1
    clt
    wbr
    #
    wa
    #
    @88
    @91
    @43
    @44
    @45
    @97
    @102
    wb
    @15
    @43
    @71
    @90
    @54
    ad2antrr
    #
    @15
    @44
    @71
    @90
    @56
    ad2antrr
    #
    @57
    @45
    @91
    1rp
    @58
    mp1i
    @85
    @25
    @22
    c1
    @24
    elbl
    syl3anc
    @91
    @101
    @88
    @99
    @91
    @87
    c1
    clt
    wbr
    #
    @87
    c1
    cle
    wbr
    #
    @101
    @88
    @91
    @87
    cr
    wcel
    #
    c1
    cr
    wcel
    @105
    @106
    wi
    @91
    @47
    @99
    @107
    @15
    @47
    @71
    @90
    @14
    @47
    @9
    @14
    @12
    @47
    @14
    @0
    cnlm
    cT
    @13
    @1
    @2
    @3
    @6
    simpl2
    sseldi
    @50
    syl
    adantr
    #
    ad2antrr
    #
    @72
    @19
    @24
    @76
    cF
    @72
    @6
    @66
    @15
    @6
    @71
    @4
    @6
    @9
    simplr
    adantr
    #
    @68
    syl
    ffvelrnda
    #
    @85
    cT
    @86
    @24
    @52
    @86
    eqid
    #
    nmcl
    syl2anc
    #
    1re
    @87
    c1
    ltle
    sylancl
    @91
    @87
    @100
    c1
    clt
    @91
    @87
    @85
    @22
    @25
    co
    #
    @100
    @91
    cT
    cgrp
    wcel
    #
    @99
    @87
    @114
    wceq
    @91
    @47
    @115
    @109
    cT
    ngpgrp
    syl
    @111
    @85
    @23
    @25
    @86
    cT
    @24
    @22
    @112
    @52
    @55
    @23
    eqid
    @53
    nmval2
    syl2anc
    @91
    @43
    @99
    @44
    @114
    @100
    wceq
    @103
    @111
    @104
    @85
    @22
    @25
    @24
    xmetsym
    syl3anc
    eqtrd
    breq1d
    @91
    @87
    c1
    @17
    @113
    @91
    1red
    @15
    @71
    @90
    simplr
    lediv1d
    3imtr3d
    adantld
    sylbid
    adantld
    sylbid
    imim12d
    ralimdva
    @72
    @28
    @78
    vy
    @19
    crab
    #
    @27
    wss
    @81
    @72
    @21
    @116
    @27
    @72
    @30
    @59
    @17
    cxr
    wcel
    #
    @21
    @116
    wceq
    @15
    @30
    @71
    @41
    adantr
    @15
    @59
    @71
    @63
    adantr
    @71
    @117
    @15
    @17
    rpxr
    adantl
    vy
    @20
    @16
    @17
    @19
    blval
    syl3anc
    sseq1d
    @78
    vy
    @19
    @27
    rabss
    syl6bb
    @72
    vy
    @74
    @17
    cS
    cT
    cF
    cG
    cB
    @82
    @86
    @73
    @19
    @73
    eqid
    #
    @39
    @96
    @112
    nmhmcn.g
    nmhmcn.b
    @15
    @1
    @71
    @35
    adantr
    @15
    @2
    @71
    @48
    adantr
    @110
    @72
    @74
    @71
    @74
    crp
    wcel
    @15
    @17
    rpreccl
    #
    adantl
    rpxrd
    @15
    @71
    simpr
    @14
    @3
    @9
    @71
    @1
    @2
    @3
    @6
    simpl3
    ad2antrr
    nmoleub2b
    3imtr4d
    @15
    @34
    @47
    @64
    w3a
    #
    @74
    cr
    wcel
    #
    @75
    @7
    wi
    @71
    @15
    @34
    @47
    @64
    @94
    @108
    @65
    3jca
    @71
    @74
    @119
    rpred
    @120
    @121
    @75
    @7
    @74
    cS
    cT
    cF
    @73
    @118
    bddnghm
    expr
    syl2an
    syld
    rexlimdva
    mpd
    ex
    impbid2
    pm5.32da
    bitrd
end
