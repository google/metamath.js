include "clnr.mm"
include "wcel.mm"
include "crg.mm"
include "cv.mm"
include "crsp.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "clidl.mm"
include "wral.mm"
include "lnrring.mm"
include "ply1ring.mm"
include "syl.mm"
include "wa.mm"
include "cldgis.mm"
include "cuz.mm"
include "cn0.mm"
include "cnacs.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "eqid.mm"
include "islnr3.mm"
include "simprbi.mm"
include "adantr.mm"
include "hbtlem7.mm"
include "sylan.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simpr.mm"
include "peano2nn0.mm"
include "adantl.mm"
include "cle.mm"
include "wbr.mm"
include "nn0re.mm"
include "lep1d.mm"
include "hbtlem4.mm"
include "ralrimiva.mm"
include "nacsfix.mm"
include "syl3anc.mm"
include "cc0.mm"
include "cfz.mm"
include "wex.mm"
include "fzfi.mm"
include "simpll.mm"
include "elfznn0.mm"
include "hbtlem6.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "sseq2d.mm"
include "ac6sfi.mm"
include "sylancr.mm"
include "crn.mm"
include "cuni.mm"
include "frn.mm"
include "ad2antrl.mm"
include "inss1.mm"
include "syl6ss.mm"
include "unissd.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "simpllr.mm"
include "lidlss.mm"
include "sstrd.mm"
include "fvex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ciun.mm"
include "wfn.mm"
include "simprl.mm"
include "ffn.mm"
include "fniunfv.mm"
include "3syl.mm"
include "inss2.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "iunfi.mm"
include "eqeltrrd.mm"
include "elind.mm"
include "ad3antrrr.mm"
include "rspcl.mm"
include "syl2anc.mm"
include "rspssp.mm"
include "cr.mm"
include "simplrl.mm"
include "nn0red.mm"
include "simprr.mm"
include "wb.mm"
include "fznn0.mm"
include "mpbir2and.mm"
include "simplrr.mm"
include "weq.mm"
include "id.mm"
include "fveq12d.mm"
include "sseq12d.mm"
include "rspcva.mm"
include "fvssunirn.mm"
include "syl5ss.mm"
include "rspssid.mm"
include "hbtlem3.mm"
include "anassrs.mm"
include "cz.mm"
include "nn0z.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "eqeq1d.mm"
include "leidd.mm"
include "wi.mm"
include "expr.mm"
include "breq1.mm"
include "imbi12d.mm"
include "mpd.mm"
include "eqsstrd.mm"
include "lecasei.mm"
include "hbtlem5.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "exlimddv.mm"
include "rexlimddv.mm"
include "islnr2.mm"
include "sylanbrc.mm"

theorem hbt
  let cP: class P
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vd: setvar d
  assume hbt.p: |- P = ( Poly1 ` R )


  assert |- ( R e. LNoeR -> P e. LNoeR )

  proof
    cR
    clnr
    wcel
    #
    cP
    crg
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cP
    crsp
    cfv
    #
    cfv
    #
    wceq
    #
    vb
    cP
    cbs
    cfv
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    va
    cP
    clidl
    cfv
    #
    wral
    cP
    clnr
    wcel
    @0
    cR
    crg
    wcel
    #
    @1
    cR
    lnrring
    #
    cP
    cR
    hbt.p
    ply1ring
    #
    syl
    #
    @0
    @10
    va
    @11
    @0
    @2
    @11
    wcel
    #
    wa
    #
    vd
    cv
    #
    @2
    cR
    cldgis
    cfv
    #
    cfv
    #
    cfv
    #
    vc
    cv
    #
    @20
    cfv
    #
    wceq
    #
    vd
    @22
    cuz
    cfv
    #
    wral
    #
    @10
    vc
    cn0
    @17
    cR
    clidl
    cfv
    #
    cR
    cbs
    cfv
    #
    cnacs
    cfv
    wcel
    #
    cn0
    @27
    @20
    wf
    #
    @3
    @20
    cfv
    @3
    c1
    caddc
    co
    #
    @20
    cfv
    wss
    #
    vb
    cn0
    wral
    @26
    vc
    cn0
    wrex
    @0
    @29
    @16
    @0
    @12
    @29
    @28
    cR
    @27
    @28
    eqid
    @27
    eqid
    #
    islnr3
    simprbi
    adantr
    @0
    @12
    @16
    @30
    @13
    cP
    cR
    @19
    @27
    @11
    @2
    hbt.p
    @11
    eqid
    #
    @19
    eqid
    #
    @33
    hbtlem7
    sylan
    @17
    @32
    vb
    cn0
    @17
    @3
    cn0
    wcel
    #
    wa
    cP
    cR
    @19
    @11
    @2
    @3
    @31
    hbt.p
    @34
    @35
    @0
    @12
    @16
    @36
    @13
    ad2antrr
    @0
    @16
    @36
    simplr
    @17
    @36
    simpr
    @36
    @31
    cn0
    wcel
    @17
    @3
    peano2nn0
    adantl
    @36
    @3
    @31
    cle
    wbr
    @17
    @36
    @3
    @3
    nn0re
    lep1d
    adantl
    hbtlem4
    ralrimiva
    vb
    vc
    vd
    @27
    @20
    @28
    nacsfix
    syl3anc
    @17
    @22
    cn0
    wcel
    #
    @26
    wa
    #
    wa
    #
    cc0
    @22
    cfz
    co
    #
    @2
    cpw
    #
    cfn
    cin
    #
    vf
    cv
    #
    wf
    #
    ve
    cv
    #
    @20
    cfv
    #
    @45
    @45
    @43
    cfv
    #
    @4
    cfv
    #
    @19
    cfv
    #
    cfv
    #
    wss
    #
    ve
    @40
    wral
    #
    wa
    #
    @10
    vf
    @17
    @53
    vf
    wex
    #
    @38
    @17
    @40
    cfn
    wcel
    #
    @46
    @45
    @5
    @19
    cfv
    #
    cfv
    #
    wss
    #
    vb
    @42
    wrex
    #
    ve
    @40
    wral
    @54
    cc0
    @22
    fzfi
    #
    @17
    @59
    ve
    @40
    @17
    @45
    @40
    wcel
    #
    wa
    cP
    cR
    @19
    @11
    vb
    @2
    @4
    @45
    hbt.p
    @34
    @35
    @4
    eqid
    #
    @0
    @16
    @61
    simpll
    @0
    @16
    @61
    simplr
    @61
    @45
    cn0
    wcel
    @17
    @45
    @22
    elfznn0
    adantl
    hbtlem6
    ralrimiva
    @58
    @51
    ve
    vb
    @40
    @42
    vf
    @3
    @47
    wceq
    #
    @57
    @50
    @46
    @63
    @45
    @56
    @49
    @63
    @5
    @48
    @19
    @3
    @47
    @4
    fveq2
    fveq2d
    fveq1d
    sseq2d
    ac6sfi
    sylancr
    adantr
    @39
    @53
    wa
    #
    @43
    crn
    #
    cuni
    #
    @9
    wcel
    @2
    @66
    @4
    cfv
    #
    wceq
    #
    @10
    @64
    @8
    cfn
    @66
    @64
    @66
    @7
    wss
    #
    @66
    @8
    wcel
    @64
    @66
    @2
    @7
    @64
    @66
    @41
    cuni
    @2
    @64
    @65
    @41
    @64
    @65
    @42
    @41
    @44
    @65
    @42
    wss
    @39
    @52
    @40
    @42
    @43
    frn
    ad2antrl
    @41
    cfn
    inss1
    syl6ss
    unissd
    @2
    unipw
    syl6sseq
    #
    @64
    @16
    @2
    @7
    wss
    @0
    @16
    @38
    @53
    simpllr
    #
    @7
    @2
    @11
    cP
    @7
    eqid
    #
    @34
    lidlss
    syl
    sstrd
    #
    @66
    @7
    cP
    cbs
    fvex
    elpw2
    sylibr
    @64
    vg
    @40
    vg
    cv
    #
    @43
    cfv
    #
    ciun
    #
    @66
    cfn
    @64
    @44
    @43
    @40
    wfn
    @76
    @66
    wceq
    @39
    @44
    @52
    simprl
    #
    @40
    @42
    @43
    ffn
    vg
    @40
    @43
    fniunfv
    3syl
    @64
    @55
    @75
    cfn
    wcel
    #
    vg
    @40
    wral
    @76
    cfn
    wcel
    @60
    @64
    @78
    vg
    @40
    @64
    @74
    @40
    wcel
    #
    wa
    @42
    cfn
    @75
    @41
    cfn
    inss2
    @64
    @40
    @42
    @74
    @43
    @77
    ffvelrnda
    sseldi
    ralrimiva
    vg
    @40
    @75
    iunfi
    sylancr
    eqeltrrd
    elind
    @64
    @67
    @2
    @64
    vg
    cP
    cR
    @19
    @11
    @67
    @2
    hbt.p
    @34
    @35
    @0
    @12
    @16
    @38
    @53
    @13
    ad3antrrr
    #
    @64
    @1
    @69
    @67
    @11
    wcel
    #
    @0
    @1
    @16
    @38
    @53
    @15
    ad3antrrr
    #
    @73
    @7
    cP
    @11
    @66
    @4
    @62
    @72
    @34
    rspcl
    syl2anc
    #
    @71
    @64
    @1
    @16
    @66
    @2
    wss
    @67
    @2
    wss
    @82
    @71
    @70
    cP
    @11
    @66
    @2
    @4
    @62
    @34
    rspssp
    syl3anc
    @64
    @74
    @20
    cfv
    #
    @74
    @67
    @19
    cfv
    #
    cfv
    #
    wss
    #
    vg
    cn0
    @64
    @74
    cn0
    wcel
    #
    wa
    #
    @87
    @74
    @22
    @88
    @74
    cr
    wcel
    @64
    @74
    nn0re
    adantl
    @89
    @22
    @64
    @37
    @88
    @17
    @37
    @26
    @53
    simplrl
    #
    adantr
    nn0red
    @64
    @88
    @74
    @22
    cle
    wbr
    #
    @87
    @64
    @88
    @91
    wa
    #
    wa
    #
    @84
    @74
    @75
    @4
    cfv
    #
    @19
    cfv
    #
    cfv
    #
    @86
    @93
    @79
    @52
    @84
    @96
    wss
    #
    @93
    @79
    @88
    @91
    @64
    @88
    @91
    simprl
    #
    @64
    @88
    @91
    simprr
    @93
    @37
    @79
    @92
    wb
    @64
    @37
    @92
    @90
    adantr
    @74
    @22
    fznn0
    syl
    mpbir2and
    @39
    @44
    @52
    @92
    simplrr
    @51
    @97
    ve
    @74
    @40
    ve
    vg
    weq
    #
    @46
    @84
    @50
    @96
    @45
    @74
    @20
    fveq2
    @99
    @45
    @74
    @49
    @95
    @99
    @48
    @94
    @19
    @99
    @47
    @75
    @4
    @45
    @74
    @43
    fveq2
    fveq2d
    fveq2d
    @99
    id
    fveq12d
    sseq12d
    rspcva
    syl2anc
    @93
    cP
    cR
    @19
    @11
    @94
    @67
    @74
    hbt.p
    @34
    @35
    @64
    @12
    @92
    @80
    adantr
    @64
    @94
    @11
    wcel
    #
    @92
    @64
    @1
    @75
    @7
    wss
    @100
    @82
    @64
    @75
    @66
    @7
    @43
    @74
    fvssunirn
    #
    @73
    syl5ss
    @7
    cP
    @11
    @75
    @4
    @62
    @72
    @34
    rspcl
    syl2anc
    adantr
    @64
    @81
    @92
    @83
    adantr
    #
    @93
    @1
    @81
    @75
    @67
    wss
    @94
    @67
    wss
    @64
    @1
    @92
    @64
    @12
    @1
    @80
    @14
    syl
    adantr
    @102
    @93
    @75
    @66
    @67
    @101
    @64
    @66
    @67
    wss
    #
    @92
    @64
    @1
    @69
    @103
    @82
    @73
    @7
    cP
    @66
    @4
    @62
    @72
    rspssid
    syl2anc
    adantr
    syl5ss
    cP
    @11
    @75
    @67
    @4
    @62
    @34
    rspssp
    syl3anc
    @98
    hbtlem3
    sstrd
    #
    anassrs
    @64
    @88
    @22
    @74
    cle
    wbr
    #
    @87
    @64
    @88
    @105
    wa
    #
    wa
    #
    @84
    @23
    @86
    @107
    @74
    @25
    wcel
    #
    @26
    @84
    @23
    wceq
    #
    @64
    @37
    @106
    @108
    @90
    @37
    @106
    wa
    @22
    cz
    wcel
    #
    @74
    cz
    wcel
    #
    @105
    @108
    @37
    @110
    @106
    @22
    nn0z
    adantr
    @88
    @111
    @37
    @105
    @74
    nn0z
    ad2antrl
    @37
    @88
    @105
    simprr
    @22
    @74
    eluz2
    syl3anbrc
    sylan
    @39
    @26
    @53
    @106
    @17
    @37
    @26
    simprr
    ad2antrr
    @24
    @109
    vd
    @74
    @25
    vd
    vg
    weq
    @21
    @84
    @23
    @18
    @74
    @20
    fveq2
    eqeq1d
    rspcva
    syl2anc
    @107
    @23
    @22
    @85
    cfv
    #
    @86
    @64
    @23
    @112
    wss
    #
    @106
    @64
    @22
    @22
    cle
    wbr
    #
    @113
    @64
    @22
    @64
    @22
    @90
    nn0red
    leidd
    @64
    @37
    @91
    @87
    wi
    #
    vg
    cn0
    wral
    @114
    @113
    wi
    #
    @90
    @64
    @115
    vg
    cn0
    @64
    @88
    @91
    @87
    @104
    expr
    ralrimiva
    @115
    @116
    vg
    @22
    cn0
    vg
    vc
    weq
    #
    @91
    @114
    @87
    @113
    @74
    @22
    @22
    cle
    breq1
    @117
    @84
    @23
    @86
    @112
    @74
    @22
    @20
    fveq2
    @74
    @22
    @85
    fveq2
    sseq12d
    imbi12d
    rspcva
    syl2anc
    mpd
    adantr
    @107
    cP
    cR
    @19
    @11
    @67
    @22
    @74
    hbt.p
    @34
    @35
    @64
    @12
    @106
    @80
    adantr
    @64
    @81
    @106
    @83
    adantr
    @64
    @37
    @106
    @90
    adantr
    @64
    @88
    @105
    simprl
    @64
    @88
    @105
    simprr
    hbtlem4
    sstrd
    eqsstrd
    anassrs
    lecasei
    ralrimiva
    hbtlem5
    eqcomd
    @6
    @68
    vb
    @66
    @9
    @3
    @66
    wceq
    @5
    @67
    @2
    @3
    @66
    @4
    fveq2
    eqeq2d
    rspcev
    syl2anc
    exlimddv
    rexlimddv
    ralrimiva
    @7
    cP
    @11
    vb
    va
    @4
    @72
    @34
    @62
    islnr2
    sylanbrc
end
