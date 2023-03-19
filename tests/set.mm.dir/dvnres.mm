include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "cn0.mm"
include "w3a.mm"
include "cdvn.mm"
include "cfv.mm"
include "cdm.mm"
include "wceq.mm"
include "cres.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "eqeq1d.mm"
include "reseq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wss.mm"
include "recnprss.mm"
include "adantr.mm"
include "pmresg.mm"
include "dvn0.mm"
include "syl2anc.mm"
include "ssid.mm"
include "a1i.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "cnelprrecn.mm"
include "simplr.mm"
include "simprl.mm"
include "dvnbss.mm"
include "syl3anc.mm"
include "cdv.mm"
include "simprr.mm"
include "dvnp1.mm"
include "eqtr3d.mm"
include "wf.mm"
include "dvnf.mm"
include "cnex.mm"
include "elpm2.mm"
include "simprbi.mm"
include "syl.mm"
include "sstrd.mm"
include "dvbss.mm"
include "eqsstrd.mm"
include "eqssd.mm"
include "expr.mm"
include "imim1d.mm"
include "oveq2.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "simpll.mm"
include "cnt.mm"
include "ctop.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "ntrss2.mm"
include "sylancr.mm"
include "crest.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "dvbssntr.mm"
include "wb.mm"
include "isopn3.mm"
include "mpbird.mm"
include "eqtr2d.mm"
include "dvres3a.mm"
include "syl22anc.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "nn0ind.mm"
include "com12.mm"
include "3impia.mm"
include "imp.mm"

theorem dvnres
  let cS: class S
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let vs: setvar s


  assert |- ( ( ( S e. { RR , CC } /\ F e. ( CC ^pm CC ) /\ N e. NN0 ) /\ dom ( ( CC Dn F ) ` N ) = dom F ) -> ( ( S Dn ( F |` S ) ) ` N ) = ( ( ( CC Dn F ) ` N ) |` S ) )

  proof
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cc
    cpm
    co
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    cN
    cc
    cF
    cdvn
    co
    #
    cfv
    #
    cdm
    #
    cF
    cdm
    #
    wceq
    #
    cN
    cS
    cF
    cS
    cres
    #
    cdvn
    co
    #
    cfv
    #
    @5
    cS
    cres
    #
    wceq
    #
    @1
    @2
    @3
    @8
    @13
    wi
    #
    @3
    @1
    @2
    wa
    #
    @14
    @15
    vx
    cv
    #
    @4
    cfv
    #
    cdm
    #
    @7
    wceq
    #
    @16
    @10
    cfv
    #
    @17
    cS
    cres
    #
    wceq
    #
    wi
    #
    wi
    @15
    cc0
    @4
    cfv
    #
    cdm
    #
    @7
    wceq
    #
    cc0
    @10
    cfv
    #
    @24
    cS
    cres
    #
    wceq
    #
    wi
    #
    wi
    @15
    vn
    cv
    #
    @4
    cfv
    #
    cdm
    #
    @7
    wceq
    #
    @31
    @10
    cfv
    #
    @32
    cS
    cres
    #
    wceq
    #
    wi
    #
    wi
    @15
    @31
    c1
    caddc
    co
    #
    @4
    cfv
    #
    cdm
    #
    @7
    wceq
    #
    @39
    @10
    cfv
    #
    @40
    cS
    cres
    #
    wceq
    #
    wi
    #
    wi
    @15
    @14
    wi
    vx
    vn
    cN
    @16
    cc0
    wceq
    #
    @23
    @30
    @15
    @47
    @19
    @26
    @22
    @29
    @47
    @18
    @25
    @7
    @47
    @17
    @24
    @16
    cc0
    @4
    fveq2
    #
    dmeqd
    eqeq1d
    @47
    @20
    @27
    @21
    @28
    @16
    cc0
    @10
    fveq2
    @47
    @17
    @24
    cS
    @48
    reseq1d
    eqeq12d
    imbi12d
    imbi2d
    @16
    @31
    wceq
    #
    @23
    @38
    @15
    @49
    @19
    @34
    @22
    @37
    @49
    @18
    @33
    @7
    @49
    @17
    @32
    @16
    @31
    @4
    fveq2
    #
    dmeqd
    eqeq1d
    @49
    @20
    @35
    @21
    @36
    @16
    @31
    @10
    fveq2
    @49
    @17
    @32
    cS
    @50
    reseq1d
    eqeq12d
    imbi12d
    imbi2d
    @16
    @39
    wceq
    #
    @23
    @46
    @15
    @51
    @19
    @42
    @22
    @45
    @51
    @18
    @41
    @7
    @51
    @17
    @40
    @16
    @39
    @4
    fveq2
    #
    dmeqd
    eqeq1d
    @51
    @20
    @43
    @21
    @44
    @16
    @39
    @10
    fveq2
    @51
    @17
    @40
    cS
    @52
    reseq1d
    eqeq12d
    imbi12d
    imbi2d
    @16
    cN
    wceq
    #
    @23
    @14
    @15
    @53
    @19
    @8
    @22
    @13
    @53
    @18
    @6
    @7
    @53
    @17
    @5
    @16
    cN
    @4
    fveq2
    #
    dmeqd
    eqeq1d
    @53
    @20
    @11
    @21
    @12
    @16
    cN
    @10
    fveq2
    @53
    @17
    @5
    cS
    @54
    reseq1d
    eqeq12d
    imbi12d
    imbi2d
    @15
    @29
    @26
    @15
    @27
    @9
    @28
    @15
    cS
    cc
    wss
    #
    @9
    cc
    cS
    cpm
    co
    wcel
    #
    @27
    @9
    wceq
    @1
    @55
    @2
    cS
    recnprss
    adantr
    #
    cc
    cS
    cc
    cF
    @0
    pmresg
    #
    cS
    @9
    dvn0
    syl2anc
    @15
    @24
    cF
    cS
    @1
    cc
    cc
    wss
    #
    @2
    @24
    cF
    wceq
    @59
    @1
    cc
    ssid
    #
    a1i
    cc
    cF
    dvn0
    sylan
    reseq1d
    eqtr4d
    a1d
    @31
    cn0
    wcel
    #
    @15
    @38
    @46
    @15
    @61
    @38
    @46
    wi
    @15
    @61
    wa
    #
    @38
    @42
    @37
    wi
    @46
    @62
    @42
    @34
    @37
    @15
    @61
    @42
    @34
    @15
    @61
    @42
    wa
    #
    wa
    #
    @33
    @7
    @64
    cc
    @0
    wcel
    #
    @2
    @61
    @33
    @7
    wss
    @65
    @64
    cnelprrecn
    a1i
    #
    @1
    @2
    @63
    simplr
    #
    @15
    @61
    @42
    simprl
    #
    cc
    cF
    @31
    dvnbss
    syl3anc
    #
    @64
    @7
    cc
    @32
    cdv
    co
    #
    cdm
    #
    @33
    @64
    @41
    @7
    @71
    @15
    @61
    @42
    simprr
    @64
    @40
    @70
    @64
    @59
    @2
    @61
    @40
    @70
    wceq
    @59
    @64
    @60
    a1i
    #
    @67
    @68
    cc
    cF
    @31
    dvnp1
    syl3anc
    #
    dmeqd
    eqtr3d
    #
    @64
    @33
    cc
    @32
    @72
    @64
    @65
    @2
    @61
    @33
    cc
    @32
    wf
    #
    @66
    @67
    @68
    cc
    cF
    @31
    dvnf
    syl3anc
    #
    @64
    @33
    @7
    cc
    @69
    @64
    @2
    @7
    cc
    wss
    #
    @67
    @2
    @7
    cc
    cF
    wf
    @77
    cc
    cc
    cF
    cnex
    cnex
    elpm2
    simprbi
    syl
    sstrd
    #
    dvbss
    eqsstrd
    eqssd
    #
    expr
    imim1d
    @62
    @42
    @37
    @45
    @15
    @61
    @42
    @37
    @45
    wi
    @37
    @45
    @64
    cS
    @35
    cdv
    co
    #
    cS
    @36
    cdv
    co
    #
    wceq
    @35
    @36
    cS
    cdv
    oveq2
    @64
    @43
    @80
    @44
    @81
    @64
    @55
    @56
    @61
    @43
    @80
    wceq
    @15
    @55
    @63
    @57
    adantr
    @15
    @56
    @63
    @58
    adantr
    @68
    cS
    @9
    @31
    dvnp1
    syl3anc
    @64
    @44
    @70
    cS
    cres
    #
    @81
    @64
    @40
    @70
    cS
    @73
    reseq1d
    @64
    @1
    @75
    @33
    ccnfld
    ctopn
    cfv
    #
    wcel
    #
    @71
    @33
    wceq
    @81
    @82
    wceq
    @1
    @2
    @63
    simpll
    @76
    @64
    @84
    @33
    @83
    cnt
    cfv
    cfv
    #
    @33
    wceq
    #
    @64
    @85
    @33
    @64
    @83
    ctop
    wcel
    #
    @33
    cc
    wss
    #
    @85
    @33
    wss
    @83
    @83
    eqid
    #
    cnfldtop
    #
    @78
    @33
    @83
    cc
    cc
    @83
    @83
    @89
    cnfldtopon
    toponunii
    #
    ntrss2
    sylancr
    @64
    @33
    @7
    @85
    @69
    @64
    @7
    @71
    @85
    @74
    @64
    @33
    cc
    @32
    @83
    @83
    @72
    @76
    @78
    @83
    cc
    crest
    co
    #
    @83
    @87
    @92
    @83
    wceq
    @90
    @83
    ctop
    cc
    @91
    restid
    ax-mp
    eqcomi
    @89
    dvbssntr
    eqsstrd
    sstrd
    eqssd
    @64
    @87
    @88
    @84
    @86
    wb
    @90
    @78
    @33
    @83
    cc
    @91
    isopn3
    sylancr
    mpbird
    @64
    @33
    @7
    @71
    @79
    @74
    eqtr2d
    @33
    cS
    @32
    @83
    @89
    dvres3a
    syl22anc
    eqtr4d
    eqeq12d
    syl5ibr
    expr
    a2d
    syld
    expcom
    a2d
    nn0ind
    com12
    3impia
    imp
end
