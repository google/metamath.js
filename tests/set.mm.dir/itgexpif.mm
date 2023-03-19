include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "cioo.mm"
include "co.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "cv.mm"
include "ce.mm"
include "cfv.mm"
include "citg.mm"
include "wa.mm"
include "wral.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "cc.mm"
include "cr.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sseli.mm"
include "mul02d.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "mul01i.mm"
include "syl6eq.mm"
include "ef0.mm"
include "sylan9eq.mm"
include "ralrimiva.mm"
include "itgeq2.mm"
include "syl.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "0re.mm"
include "1re.mm"
include "ioovolcl.mm"
include "mp2an.mm"
include "ax-1cn.mm"
include "itgconst.mm"
include "mp3an.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "0le1.mm"
include "volioo.mm"
include "subid1i.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "mulid1i.mm"
include "3eqtri.mm"
include "adantl.mm"
include "eqcomd.mm"
include "wn.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmnf.mm"
include "cpnf.mm"
include "ioomax.mm"
include "eqcomi.mm"
include "0red.mm"
include "1red.mm"
include "a1i.mm"
include "wss.mm"
include "sselda.mm"
include "2cnd.mm"
include "mulcld.mm"
include "simpl.mm"
include "zcnd.mm"
include "adantr.mm"
include "simpr.mm"
include "efcld.mm"
include "syldan.mm"
include "wne.mm"
include "ine0.mm"
include "2ne0.mm"
include "pipos.mm"
include "gtneii.mm"
include "mulne0i.mm"
include "neqned.mm"
include "mulne0d.mm"
include "divcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "ccncf.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "cnelprrecn.mm"
include "dvmptid.mm"
include "dvmptcmul.mm"
include "mulid1d.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "dvef.mm"
include "wf.mm"
include "eff.mm"
include "feqmptd.mm"
include "3eqtr3a.mm"
include "dvmptdivc.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "dvmptco.mm"
include "divcan1d.mm"
include "efcn.mm"
include "cres.mm"
include "resmpt.mm"
include "mp1i.mm"
include "mulc1cncf.mm"
include "wi.mm"
include "rescncf.mm"
include "mpd.mm"
include "eqeltrrd.mm"
include "cncfmpt1f.mm"
include "eqeltrd.mm"
include "ftc2re.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "fvmpt2d.mm"
include "mulassd.mm"
include "sylan2.mm"
include "eqidd.mm"
include "fvmptd.mm"
include "ef2kpi.mm"
include "sseldi.mm"
include "mul01d.mm"
include "oveq12d.mm"
include "subidd.mm"
include "3eqtr3d.mm"
include "ifeqda.mm"

theorem itgexpif
  let vx: setvar x
  let cN: class N
  let vy: setvar y
  let vz: setvar z

  disjoint N x
  disjoint N y
  disjoint N z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( N e. ZZ -> S. ( 0 (,) 1 ) ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. ( N x. x ) ) ) _d x = if ( N = 0 , 1 , 0 ) )

  proof
    cN
    cz
    wcel
    #
    cN
    cc0
    wceq
    #
    c1
    cc0
    cif
    vx
    cc0
    c1
    cioo
    co
    #
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cN
    vx
    cv
    #
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    citg
    #
    @0
    @1
    c1
    cc0
    @9
    @0
    @1
    wa
    @9
    c1
    @1
    @9
    c1
    wceq
    @0
    @1
    @9
    vx
    @2
    c1
    citg
    #
    c1
    @1
    @8
    c1
    wceq
    #
    vx
    @2
    wral
    @9
    @10
    wceq
    @1
    @11
    vx
    @2
    @1
    @5
    @2
    wcel
    #
    @8
    @4
    cc0
    @5
    cmul
    co
    #
    cmul
    co
    #
    ce
    cfv
    #
    c1
    @1
    @7
    @14
    ce
    @1
    @6
    @13
    @4
    cmul
    cN
    cc0
    @5
    cmul
    oveq1
    oveq2d
    fveq2d
    @12
    @15
    cc0
    ce
    cfv
    #
    c1
    @12
    @14
    cc0
    ce
    @12
    @14
    @4
    cc0
    cmul
    co
    cc0
    @12
    @13
    cc0
    @4
    cmul
    @12
    @5
    @2
    cc
    @5
    @2
    cr
    cc
    cc0
    c1
    ioossre
    #
    ax-resscn
    sstri
    sseli
    mul02d
    oveq2d
    @4
    ci
    @3
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    #
    mulcli
    #
    mul01i
    syl6eq
    fveq2d
    ef0
    syl6eq
    sylan9eq
    ralrimiva
    vx
    @2
    @8
    c1
    itgeq2
    syl
    @10
    c1
    @2
    cvol
    cfv
    #
    cmul
    co
    #
    c1
    c1
    cmul
    co
    c1
    @2
    cvol
    cdm
    wcel
    @20
    cr
    wcel
    #
    c1
    cc
    wcel
    #
    @10
    @21
    wceq
    cc0
    c1
    ioombl
    cc0
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @22
    0re
    1re
    cc0
    c1
    ioovolcl
    mp2an
    ax-1cn
    vx
    @2
    c1
    itgconst
    mp3an
    @20
    c1
    c1
    cmul
    @20
    c1
    cc0
    cmin
    co
    #
    c1
    @24
    @25
    cc0
    c1
    cle
    wbr
    #
    @20
    @26
    wceq
    0re
    1re
    0le1
    cc0
    c1
    volioo
    mp3an
    c1
    ax-1cn
    subid1i
    eqtri
    oveq2i
    c1
    ax-1cn
    mulid1i
    3eqtri
    syl6eq
    adantl
    eqcomd
    @0
    @1
    wn
    #
    wa
    #
    @9
    cc0
    @29
    vx
    @2
    @5
    cr
    vy
    cr
    @4
    cN
    cmul
    co
    #
    vy
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @30
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    #
    cfv
    #
    citg
    #
    c1
    @35
    cfv
    #
    cc0
    @35
    cfv
    #
    cmin
    co
    #
    @9
    cc0
    @29
    vx
    cc0
    c1
    cmnf
    cpnf
    cr
    @35
    cmnf
    cpnf
    cioo
    co
    cr
    ioomax
    eqcomi
    @29
    0red
    #
    @29
    1red
    #
    @27
    @29
    0le1
    a1i
    @29
    vy
    cr
    @34
    cc
    @35
    @29
    @31
    cr
    wcel
    #
    wa
    #
    @33
    @30
    @29
    @44
    @31
    cc
    wcel
    #
    @33
    cc
    wcel
    @29
    cr
    cc
    @31
    cr
    cc
    wss
    #
    @29
    ax-resscn
    a1i
    #
    sselda
    #
    @29
    @46
    wa
    #
    @32
    @50
    @30
    @31
    @29
    @30
    cc
    wcel
    #
    @46
    @29
    @4
    cN
    @29
    ci
    @3
    ci
    cc
    wcel
    @29
    ax-icn
    a1i
    @29
    c2
    cpi
    @29
    2cnd
    cpi
    cc
    wcel
    @29
    picn
    a1i
    mulcld
    mulcld
    #
    @29
    cN
    @0
    @28
    simpl
    #
    zcnd
    #
    mulcld
    #
    adantr
    @29
    @46
    simpr
    mulcld
    efcld
    syldan
    #
    @29
    @51
    @44
    @55
    adantr
    #
    @29
    @30
    cc0
    wne
    #
    @44
    @29
    @4
    cN
    @52
    @54
    @4
    cc0
    wne
    @29
    ci
    @3
    ax-icn
    @18
    ine0
    c2
    cpi
    2cn
    picn
    2ne0
    cc0
    cpi
    0re
    pipos
    gtneii
    mulne0i
    mulne0i
    a1i
    @29
    cN
    cc0
    @0
    @28
    simpr
    neqned
    mulne0d
    #
    adantr
    #
    divcld
    @35
    eqid
    fmptd
    @29
    @36
    vy
    cr
    @33
    cmpt
    #
    cr
    cc
    ccncf
    co
    #
    @29
    @36
    vy
    cr
    @34
    @30
    cmul
    co
    #
    cmpt
    @61
    @29
    vy
    vz
    @32
    @30
    vz
    cv
    #
    ce
    cfv
    #
    @30
    cdiv
    co
    #
    @66
    cr
    cc
    @34
    @34
    cc
    cc
    cr
    cc
    cr
    cr
    cc
    cpr
    #
    wcel
    @29
    reelprrecn
    a1i
    #
    cc
    @67
    wcel
    @29
    cnelprrecn
    a1i
    #
    @45
    @30
    @31
    @57
    @49
    mulcld
    @57
    @29
    @64
    cc
    wcel
    #
    wa
    #
    @65
    @30
    @71
    @64
    @29
    @70
    simpr
    efcld
    #
    @29
    @51
    @70
    @55
    adantr
    @29
    @58
    @70
    @59
    adantr
    divcld
    #
    @73
    @29
    cr
    vy
    cr
    @32
    cmpt
    #
    cdv
    co
    vy
    cr
    @30
    c1
    cmul
    co
    #
    cmpt
    vy
    cr
    @30
    cmpt
    @29
    vy
    @31
    c1
    @30
    cr
    cr
    cr
    @68
    @49
    @25
    @45
    1re
    a1i
    @29
    vy
    cr
    @68
    dvmptid
    @55
    dvmptcmul
    @29
    vy
    cr
    @75
    @30
    @45
    @30
    @57
    mulid1d
    mpteq2dva
    eqtrd
    @29
    vz
    @65
    @65
    @30
    cc
    cc
    cc
    @69
    @72
    @72
    @29
    cc
    ce
    cdv
    co
    ce
    cc
    vz
    cc
    @65
    cmpt
    #
    cdv
    co
    @76
    dvef
    @29
    ce
    @76
    cc
    cdv
    @29
    vz
    cc
    cc
    ce
    cc
    cc
    ce
    wf
    @29
    eff
    a1i
    feqmptd
    #
    oveq2d
    @77
    3eqtr3a
    @55
    @59
    dvmptdivc
    @64
    @32
    wceq
    @65
    @33
    @30
    cdiv
    @64
    @32
    ce
    fveq2
    oveq1d
    #
    @78
    dvmptco
    @29
    vy
    cr
    @63
    @33
    @45
    @33
    @30
    @56
    @57
    @60
    divcan1d
    mpteq2dva
    eqtrd
    #
    @29
    vy
    @32
    ce
    cr
    ce
    cc
    cc
    ccncf
    co
    #
    wcel
    @29
    efcn
    a1i
    @29
    vy
    cc
    @32
    cmpt
    #
    cr
    cres
    #
    @74
    @62
    @47
    @82
    @74
    wceq
    @29
    ax-resscn
    vy
    cc
    cr
    @32
    resmpt
    mp1i
    @29
    @81
    @80
    wcel
    #
    @82
    @62
    wcel
    #
    @29
    @51
    @83
    @55
    vy
    @30
    @81
    @81
    eqid
    mulc1cncf
    syl
    @47
    @83
    @84
    wi
    @29
    ax-resscn
    cc
    cc
    cr
    @81
    rescncf
    mp1i
    mpd
    eqeltrrd
    cncfmpt1f
    eqeltrd
    ftc2re
    @29
    @37
    @8
    wceq
    #
    vx
    @2
    wral
    @38
    @9
    wceq
    @29
    @85
    vx
    @2
    @12
    @29
    @5
    cr
    wcel
    #
    @85
    @2
    cr
    @5
    @17
    sseli
    @29
    @86
    wa
    #
    @37
    @5
    @61
    cfv
    #
    @8
    @87
    @5
    @36
    @61
    @29
    @36
    @61
    wceq
    @86
    @79
    adantr
    fveq1d
    @87
    @88
    @30
    @5
    cmul
    co
    #
    ce
    cfv
    #
    @8
    @29
    vx
    cr
    @90
    @61
    cc
    @61
    vx
    cr
    @90
    cmpt
    wceq
    @29
    vy
    vx
    cr
    @33
    @90
    @31
    @5
    wceq
    @32
    @89
    ce
    @31
    @5
    @30
    cmul
    oveq2
    fveq2d
    cbvmptv
    a1i
    @87
    @89
    @87
    @30
    @5
    @29
    @51
    @86
    @55
    adantr
    @29
    cr
    cc
    @5
    @48
    sselda
    #
    mulcld
    efcld
    fvmpt2d
    @87
    @89
    @7
    ce
    @87
    @4
    cN
    @5
    @4
    cc
    wcel
    @87
    @19
    a1i
    @29
    cN
    cc
    wcel
    @86
    @54
    adantr
    @91
    mulassd
    fveq2d
    eqtrd
    eqtrd
    sylan2
    ralrimiva
    vx
    @2
    @37
    @8
    itgeq2
    syl
    @29
    @41
    c1
    @30
    cdiv
    co
    #
    @92
    cmin
    co
    cc0
    @29
    @39
    @92
    @40
    @92
    cmin
    @29
    @39
    @75
    ce
    cfv
    #
    @30
    cdiv
    co
    #
    @92
    @29
    vy
    c1
    @34
    @94
    cr
    @35
    cc
    @29
    @35
    eqidd
    #
    @29
    @31
    c1
    wceq
    #
    wa
    #
    @33
    @93
    @30
    cdiv
    @97
    @32
    @75
    ce
    @97
    @31
    c1
    @30
    cmul
    @29
    @96
    simpr
    oveq2d
    fveq2d
    oveq1d
    @43
    @29
    @93
    @30
    @29
    @75
    @29
    @30
    c1
    @55
    @23
    @29
    ax-1cn
    a1i
    mulcld
    efcld
    @55
    @59
    divcld
    #
    fvmptd
    @29
    @93
    c1
    @30
    cdiv
    @29
    @93
    @30
    ce
    cfv
    #
    c1
    @29
    @75
    @30
    ce
    @29
    @30
    @55
    mulid1d
    fveq2d
    @29
    @0
    @99
    c1
    wceq
    @53
    cN
    ef2kpi
    syl
    eqtrd
    oveq1d
    #
    eqtrd
    @29
    @40
    @30
    cc0
    cmul
    co
    #
    ce
    cfv
    #
    @30
    cdiv
    co
    #
    @92
    @29
    vy
    cc0
    @34
    @103
    cr
    @35
    cc
    @95
    @29
    @31
    cc0
    wceq
    #
    wa
    #
    @33
    @102
    @30
    cdiv
    @105
    @32
    @101
    ce
    @105
    @31
    cc0
    @30
    cmul
    @29
    @104
    simpr
    oveq2d
    fveq2d
    oveq1d
    @42
    @29
    @102
    @30
    @29
    @101
    @29
    @30
    cc0
    @55
    @29
    cr
    cc
    cc0
    ax-resscn
    @42
    sseldi
    mulcld
    efcld
    @55
    @59
    divcld
    fvmptd
    @29
    @102
    c1
    @30
    cdiv
    @29
    @102
    @16
    c1
    @29
    @101
    cc0
    ce
    @29
    @30
    @55
    mul01d
    fveq2d
    ef0
    syl6eq
    oveq1d
    eqtrd
    oveq12d
    @29
    @92
    @29
    @94
    @92
    cc
    @100
    @98
    eqeltrrd
    subidd
    eqtrd
    3eqtr3d
    eqcomd
    ifeqda
    eqcomd
end
