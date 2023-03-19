include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cfn.mm"
include "crab.mm"
include "csubmnd.mm"
include "cmre.mm"
include "wss.mm"
include "cvv.mm"
include "elex.mm"
include "cmnd.mm"
include "cacs.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "submacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "symgtrf.mm"
include "a1i.mm"
include "wa.mm"
include "c2o.mm"
include "com.mm"
include "2onn.mm"
include "nnfi.mm"
include "ax-mp.mm"
include "wb.mm"
include "cen.mm"
include "wbr.mm"
include "wf1o.mm"
include "cpmtr.mm"
include "eqid.mm"
include "pmtrfb.mm"
include "simp3bi.mm"
include "enfi.mm"
include "adantl.mm"
include "mpbiri.mm"
include "ssrabdv.mm"
include "csubg.mm"
include "symgfisg.mm"
include "subgsubm.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "wi.mm"
include "vex.mm"
include "finnum.mm"
include "cdom.mm"
include "csdm.mm"
include "wal.mm"
include "domfi.mm"
include "c0.mm"
include "wceq.mm"
include "cres.mm"
include "wfn.mm"
include "symgbasf1o.mm"
include "f1ofn.mm"
include "fnnfpeq0.mm"
include "c0g.mm"
include "csymg.mm"
include "elbasfv.mm"
include "symgid.mm"
include "mrccl.mm"
include "sylancl.mm"
include "subm0cl.mm"
include "eqeltrd.mm"
include "eleq1a.mm"
include "sylbid.mm"
include "adantr.mm"
include "wne.mm"
include "wex.mm"
include "n0.mm"
include "cpr.mm"
include "cplusg.mm"
include "co.mm"
include "ccom.mm"
include "simpr.mm"
include "csn.mm"
include "f1omvdmvd.mm"
include "sylan.mm"
include "eldifad.mm"
include "prssi.mm"
include "syl2anc.mm"
include "difss.mm"
include "dmss.mm"
include "f1odm.mm"
include "syl5sseq.mm"
include "sstrd.mm"
include "sselda.mm"
include "fnelnfp.mm"
include "mpbid.mm"
include "necomd.mm"
include "fvex.mm"
include "pr2nelem.mm"
include "mp3an12.mm"
include "pmtrrn.mm"
include "sseldi.mm"
include "simplr.mm"
include "symgov.mm"
include "oveq2d.mm"
include "grpcl.mm"
include "eqeltrrd.mm"
include "coass.mm"
include "pmtrfinv.mm"
include "coeq1d.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi2.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "3eqtrd.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "mrcssid.mm"
include "sseldd.mm"
include "difeq1d.mm"
include "dmeqd.mm"
include "wpss.mm"
include "simpll.mm"
include "cun.mm"
include "mvdco.mm"
include "pmtrmvd.mm"
include "eqsstrd.mm"
include "ssid.mm"
include "unssd.mm"
include "syl5ss.mm"
include "wn.mm"
include "fvco2.mm"
include "prcom.mm"
include "fveq2i.mm"
include "fveq1i.mm"
include "pmtrprfv.mm"
include "syl13anc.mm"
include "syl5eq.mm"
include "necon2bbid.mm"
include "ssnelpssd.mm"
include "php3.mm"
include "eqbrtrd.mm"
include "ovex.mm"
include "difeq1.mm"
include "breq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcv.mm"
include "ad2antlr.mm"
include "mp2d.mm"
include "submcl.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "exp31.mm"
include "com23.mm"
include "3impia.mm"
include "indcardi.mm"
include "impcom.mm"
include "3adant1.mm"
include "rabssdv.mm"
include "eqssd.mm"

theorem symggen
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cT: class T
  let cG: class G
  let cK: class K
  let cV: class V
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  assume symgtrf.t: |- T = ran ( pmTrsp ` D )
  assume symgtrf.g: |- G = ( SymGrp ` D )
  assume symgtrf.b: |- B = ( Base ` G )
  assume symggen.k: |- K = ( mrCls ` ( SubMnd ` G ) )

  disjoint B x
  disjoint T x
  disjoint K x
  disjoint D x
  disjoint G x
  disjoint V x
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint K u
  disjoint K y
  disjoint K z
  disjoint T u
  disjoint T y
  disjoint T z
  disjoint D z
  disjoint G z
  assert |- ( D e. V -> ( K ` T ) = { x e. B | dom ( x \ _I ) e. Fin } )

  proof
    cD
    cV
    wcel
    #
    cT
    cK
    cfv
    #
    vx
    cv
    #
    cid
    cdif
    #
    cdm
    #
    cfn
    wcel
    #
    vx
    cB
    crab
    #
    @0
    cG
    csubmnd
    cfv
    #
    cB
    cmre
    cfv
    wcel
    #
    cT
    @6
    wss
    @6
    @7
    wcel
    #
    @1
    @6
    wss
    @0
    cD
    cvv
    wcel
    #
    @8
    cD
    cV
    elex
    @10
    cG
    cmnd
    wcel
    #
    @7
    cB
    cacs
    cfv
    wcel
    @8
    @10
    cG
    cgrp
    wcel
    #
    @11
    cD
    cG
    cvv
    symgtrf.g
    symggrp
    #
    cG
    grpmnd
    syl
    cB
    cG
    symgtrf.b
    submacs
    @7
    cB
    acsmre
    3syl
    #
    syl
    @0
    @5
    vx
    cB
    cT
    cT
    cB
    wss
    #
    @0
    cB
    cD
    cT
    cG
    symgtrf.t
    symgtrf.g
    symgtrf.b
    symgtrf
    #
    a1i
    @0
    @2
    cT
    wcel
    #
    wa
    @5
    c2o
    cfn
    wcel
    #
    c2o
    com
    wcel
    @18
    2onn
    c2o
    nnfi
    ax-mp
    @17
    @5
    @18
    wb
    #
    @0
    @17
    @4
    c2o
    cen
    wbr
    #
    @19
    @17
    @10
    cD
    cD
    @2
    wf1o
    @20
    cD
    cT
    cD
    cpmtr
    cfv
    #
    @2
    @21
    eqid
    #
    symgtrf.t
    pmtrfb
    simp3bi
    @4
    c2o
    enfi
    syl
    adantl
    mpbiri
    ssrabdv
    @0
    @6
    cG
    csubg
    cfv
    wcel
    @9
    vx
    cB
    cD
    cG
    cV
    symgtrf.g
    symgtrf.b
    symgfisg
    @6
    cG
    subgsubm
    syl
    @7
    cT
    cK
    @6
    cB
    symggen.k
    mrcsscl
    syl3anc
    @0
    @5
    vx
    cB
    @1
    @2
    cB
    wcel
    #
    @5
    @2
    @1
    wcel
    #
    @0
    @5
    @23
    @24
    @5
    vy
    cv
    #
    cB
    wcel
    #
    @25
    @1
    wcel
    #
    wi
    #
    vz
    cv
    #
    cB
    wcel
    #
    @29
    @1
    wcel
    #
    wi
    #
    @23
    @24
    wi
    vy
    vz
    @2
    @25
    cid
    cdif
    #
    cdm
    #
    @29
    cid
    cdif
    #
    cdm
    #
    @4
    cvv
    @2
    cvv
    wcel
    @5
    vx
    vex
    a1i
    @4
    finnum
    @5
    @34
    @4
    cdom
    wbr
    #
    @36
    @34
    csdm
    wbr
    #
    @32
    wi
    #
    vz
    wal
    #
    @28
    @5
    @37
    wa
    @34
    cfn
    wcel
    #
    @40
    @28
    wi
    @4
    @34
    domfi
    @41
    @26
    @40
    @27
    @41
    @26
    @40
    @27
    @41
    @26
    wa
    #
    @40
    wa
    #
    @27
    @34
    c0
    @42
    @34
    c0
    wceq
    #
    @27
    wi
    @40
    @42
    @44
    @25
    cid
    cD
    cres
    #
    wceq
    #
    @27
    @42
    cD
    cD
    @25
    wf1o
    #
    @25
    cD
    wfn
    #
    @44
    @46
    wb
    @26
    @47
    @41
    cD
    cB
    @25
    cG
    symgtrf.g
    symgtrf.b
    symgbasf1o
    adantl
    #
    cD
    cD
    @25
    f1ofn
    #
    cD
    @25
    fnnfpeq0
    3syl
    @42
    @45
    @1
    wcel
    @46
    @27
    wi
    @42
    @45
    cG
    c0g
    cfv
    #
    @1
    @42
    @10
    @45
    @51
    wceq
    @26
    @10
    @41
    cB
    cG
    csymg
    @25
    cD
    symgtrf.g
    symgtrf.b
    elbasfv
    adantl
    #
    cD
    cG
    cvv
    symgtrf.g
    symgid
    syl
    @42
    @1
    @7
    wcel
    #
    @51
    @1
    wcel
    @42
    @8
    @15
    @53
    @42
    @10
    @8
    @52
    @14
    syl
    #
    @16
    @7
    cT
    cK
    cB
    symggen.k
    mrccl
    sylancl
    #
    @1
    cG
    @51
    @51
    eqid
    subm0cl
    syl
    eqeltrd
    @45
    @1
    @25
    eleq1a
    syl
    sylbid
    adantr
    @34
    c0
    wne
    vu
    cv
    #
    @34
    wcel
    #
    vu
    wex
    @43
    @27
    vu
    @34
    n0
    @43
    @57
    @27
    vu
    @43
    @57
    @27
    @43
    @57
    wa
    #
    @56
    @56
    @25
    cfv
    #
    cpr
    #
    @21
    cfv
    #
    @61
    @25
    cG
    cplusg
    cfv
    #
    co
    #
    @62
    co
    #
    @25
    @1
    @42
    @57
    @64
    @25
    wceq
    @40
    @42
    @57
    wa
    #
    @64
    @61
    @61
    @25
    ccom
    #
    @62
    co
    #
    @61
    @66
    ccom
    #
    @25
    @65
    @63
    @66
    @61
    @62
    @65
    @61
    cB
    wcel
    #
    @26
    @63
    @66
    wceq
    @65
    cT
    cB
    @61
    @16
    @65
    @10
    @60
    cD
    wss
    #
    @60
    c2o
    cen
    wbr
    #
    @61
    cT
    wcel
    #
    @42
    @10
    @57
    @52
    adantr
    #
    @65
    @60
    @34
    cD
    @65
    @57
    @59
    @34
    wcel
    @60
    @34
    wss
    @42
    @57
    simpr
    #
    @65
    @59
    @34
    @56
    csn
    #
    @42
    @47
    @57
    @59
    @34
    @75
    cdif
    wcel
    @49
    cD
    @25
    @56
    f1omvdmvd
    sylan
    eldifad
    #
    @56
    @59
    @34
    prssi
    syl2anc
    #
    @42
    @34
    cD
    wss
    @57
    @42
    @25
    cdm
    #
    @34
    cD
    @33
    @25
    wss
    @34
    @78
    wss
    @25
    cid
    difss
    @33
    @25
    dmss
    ax-mp
    @42
    @47
    @78
    cD
    wceq
    @49
    cD
    cD
    @25
    f1odm
    syl
    syl5sseq
    #
    adantr
    #
    sstrd
    #
    @65
    @56
    @59
    wne
    #
    @71
    @65
    @59
    @56
    @65
    @57
    @59
    @56
    wne
    #
    @74
    @65
    @48
    @56
    cD
    wcel
    #
    @57
    @83
    wb
    @65
    @47
    @48
    @42
    @47
    @57
    @49
    adantr
    #
    @50
    syl
    #
    @42
    @34
    cD
    @56
    @79
    sselda
    #
    cD
    @25
    @56
    fnelnfp
    syl2anc
    mpbid
    #
    necomd
    @56
    cvv
    wcel
    @59
    cvv
    wcel
    @82
    @71
    vu
    vex
    @56
    @25
    fvex
    @56
    @59
    cvv
    cvv
    pr2nelem
    mp3an12
    syl
    #
    cD
    @60
    cT
    @21
    cvv
    @22
    symgtrf.t
    pmtrrn
    syl3anc
    #
    sseldi
    #
    @41
    @26
    @57
    simplr
    #
    cD
    cB
    @62
    cG
    @61
    @25
    symgtrf.g
    symgtrf.b
    @62
    eqid
    #
    symgov
    syl2anc
    #
    oveq2d
    @65
    @69
    @66
    cB
    wcel
    #
    @67
    @68
    wceq
    @91
    @65
    @63
    @66
    cB
    @94
    @65
    @12
    @69
    @26
    @63
    cB
    wcel
    #
    @42
    @12
    @57
    @42
    @10
    @12
    @52
    @13
    syl
    adantr
    @91
    @92
    cB
    @62
    cG
    @61
    @25
    symgtrf.b
    @93
    grpcl
    syl3anc
    #
    eqeltrrd
    #
    cD
    cB
    @62
    cG
    @61
    @66
    symgtrf.g
    symgtrf.b
    @93
    symgov
    syl2anc
    @65
    @68
    @61
    @61
    ccom
    #
    @25
    ccom
    #
    @25
    @61
    @61
    @25
    coass
    @65
    @100
    @45
    @25
    ccom
    #
    @25
    @65
    @99
    @45
    @25
    @65
    @72
    @99
    @45
    wceq
    @90
    cD
    cT
    @21
    @61
    @22
    symgtrf.t
    pmtrfinv
    syl
    coeq1d
    @65
    @47
    cD
    cD
    @25
    wf
    @101
    @25
    wceq
    @85
    cD
    cD
    @25
    f1of
    cD
    cD
    @25
    fcoi2
    3syl
    eqtrd
    syl5eqr
    3eqtrd
    adantlr
    @58
    @53
    @61
    @1
    wcel
    #
    @63
    @1
    wcel
    #
    @64
    @1
    wcel
    @42
    @53
    @40
    @57
    @55
    ad2antrr
    @42
    @57
    @102
    @40
    @65
    cT
    @1
    @61
    @42
    cT
    @1
    wss
    #
    @57
    @42
    @8
    @15
    @104
    @54
    @16
    @7
    cT
    cK
    cB
    symggen.k
    mrcssid
    sylancl
    adantr
    @90
    sseldd
    adantlr
    @58
    @63
    cid
    cdif
    #
    cdm
    #
    @34
    csdm
    wbr
    #
    @96
    @103
    @42
    @57
    @107
    @40
    @65
    @106
    @66
    cid
    cdif
    #
    cdm
    #
    @34
    csdm
    @65
    @105
    @108
    @65
    @63
    @66
    cid
    @94
    difeq1d
    dmeqd
    @65
    @41
    @109
    @34
    wpss
    @109
    @34
    csdm
    wbr
    @41
    @26
    @57
    simpll
    @65
    @109
    @34
    @56
    @65
    @109
    @61
    cid
    cdif
    cdm
    #
    @34
    cun
    @34
    @61
    @25
    mvdco
    @65
    @110
    @34
    @34
    @65
    @110
    @60
    @34
    @65
    @10
    @70
    @71
    @110
    @60
    wceq
    @73
    @81
    @89
    cD
    @60
    @21
    cvv
    @22
    pmtrmvd
    syl3anc
    @77
    eqsstrd
    @34
    @34
    wss
    @65
    @34
    ssid
    a1i
    unssd
    syl5ss
    @74
    @65
    @56
    @66
    cfv
    #
    @56
    wceq
    #
    @56
    @109
    wcel
    #
    wn
    #
    @65
    @111
    @59
    @61
    cfv
    #
    @56
    @65
    @48
    @84
    @111
    @115
    wceq
    @86
    @87
    cD
    @61
    @25
    @56
    fvco2
    syl2anc
    @65
    @115
    @59
    @59
    @56
    cpr
    #
    @21
    cfv
    #
    cfv
    #
    @56
    @59
    @61
    @117
    @60
    @116
    @21
    @56
    @59
    prcom
    fveq2i
    fveq1i
    @65
    @10
    @59
    cD
    wcel
    @84
    @83
    @118
    @56
    wceq
    @73
    @65
    @34
    cD
    @59
    @80
    @76
    sseldd
    @87
    @88
    cD
    @21
    cvv
    @59
    @56
    @22
    pmtrprfv
    syl13anc
    syl5eq
    eqtrd
    @65
    @66
    cD
    wfn
    #
    @84
    @112
    @114
    wb
    @65
    @95
    cD
    cD
    @66
    wf1o
    @119
    @98
    cD
    cB
    @66
    cG
    symgtrf.g
    symgtrf.b
    symgbasf1o
    cD
    cD
    @66
    f1ofn
    3syl
    @87
    @119
    @84
    wa
    @113
    @111
    @56
    cD
    @66
    @56
    fnelnfp
    necon2bbid
    syl2anc
    mpbid
    ssnelpssd
    @34
    @109
    php3
    syl2anc
    eqbrtrd
    adantlr
    @42
    @57
    @96
    @40
    @97
    adantlr
    @40
    @107
    @96
    @103
    wi
    #
    wi
    #
    @42
    @57
    @39
    @121
    vz
    @63
    @61
    @25
    @62
    ovex
    @29
    @63
    wceq
    #
    @38
    @107
    @32
    @120
    @122
    @36
    @106
    @34
    csdm
    @122
    @35
    @105
    @29
    @63
    cid
    difeq1
    dmeqd
    breq1d
    @122
    @30
    @96
    @31
    @103
    @29
    @63
    cB
    eleq1
    @29
    @63
    @1
    eleq1
    imbi12d
    imbi12d
    spcv
    ad2antlr
    mp2d
    @62
    @1
    cG
    @61
    @63
    @93
    submcl
    syl3anc
    eqeltrrd
    ex
    exlimdv
    syl5bi
    pm2.61dne
    exp31
    com23
    syl
    3impia
    @25
    @29
    wceq
    #
    @26
    @30
    @27
    @31
    @25
    @29
    cB
    eleq1
    @25
    @29
    @1
    eleq1
    imbi12d
    @25
    @2
    wceq
    #
    @26
    @23
    @27
    @24
    @25
    @2
    cB
    eleq1
    @25
    @2
    @1
    eleq1
    imbi12d
    @123
    @33
    @35
    @25
    @29
    cid
    difeq1
    dmeqd
    @124
    @33
    @3
    @25
    @2
    cid
    difeq1
    dmeqd
    indcardi
    impcom
    3adant1
    rabssdv
    eqssd
end
