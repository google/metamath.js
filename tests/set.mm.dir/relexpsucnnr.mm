include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crelexp.mm"
include "ccom.mm"
include "wceq.mm"
include "wi.mm"
include "cvv.mm"
include "cn0.mm"
include "cv.mm"
include "cc0.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "cif.mm"
include "eqidd.mm"
include "simprr.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "coeq2.mm"
include "mpt2eq3dv.mm"
include "id.mm"
include "mpteq2dv.mm"
include "seqeq123d.mm"
include "fveq1d.mm"
include "ifeq12d.mm"
include "ad2antrl.mm"
include "a1i.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "ifbieq2d.mm"
include "eqeq1d.mm"
include "3imtr4d.mm"
include "mpcom.mm"
include "elex.mm"
include "adantr.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "nnnn0d.mm"
include "dmexg.mm"
include "rnexg.mm"
include "unexg.mm"
include "syl2anc.mm"
include "resiexg.mm"
include "syl.mm"
include "fvexd.mm"
include "ifcld.mm"
include "ovmpt2d.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "adantl.mm"
include "seqp1.mm"
include "ovex.mm"
include "simpl.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "nfcv.mm"
include "weq.mm"
include "coeq1d.mm"
include "cbvmpt2.mm"
include "oveq.mm"
include "mp1i.mm"
include "simprl.mm"
include "fvex.mm"
include "coexg.mm"
include "fveq12d.mm"
include "ifbieq12d.mm"
include "wne.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "wb.mm"
include "df-relexp.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem relexpsucnnr
  let cR: class R
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R e. V /\ N e. NN ) -> ( R ^r ( N + 1 ) ) = ( ( R ^r N ) o. R ) )

  proof
    cR
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cR
    cN
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cR
    cN
    crelexp
    co
    #
    cR
    ccom
    #
    wceq
    #
    wi
    #
    @2
    cR
    @3
    vr
    vn
    cvv
    cn0
    vn
    cv
    #
    cc0
    wceq
    #
    cid
    vr
    cv
    #
    cdm
    #
    @11
    crn
    #
    cun
    #
    cres
    #
    @9
    vx
    vy
    cvv
    cvv
    vx
    cv
    #
    @11
    ccom
    #
    cmpt2
    #
    vz
    cvv
    @11
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    cif
    #
    cmpt2
    #
    co
    #
    cR
    cN
    @23
    co
    #
    cR
    ccom
    #
    wceq
    #
    wi
    #
    @2
    @24
    @3
    cc0
    wceq
    #
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    cres
    #
    @3
    vx
    vy
    cvv
    cvv
    @16
    cR
    ccom
    #
    cmpt2
    #
    vz
    cvv
    cR
    cmpt
    #
    c1
    cseq
    #
    cfv
    #
    cif
    #
    @38
    @26
    @2
    vr
    vn
    cR
    @3
    cvv
    cn0
    @22
    @39
    @23
    cvv
    @2
    @23
    eqidd
    #
    @9
    @3
    wceq
    #
    @2
    @11
    cR
    wceq
    #
    @41
    wa
    #
    wa
    #
    @22
    @39
    wceq
    #
    @2
    @42
    @41
    simprr
    @41
    @2
    @42
    @3
    @3
    wceq
    #
    wa
    #
    wa
    #
    @29
    @15
    @3
    @20
    cfv
    #
    cif
    #
    @39
    wceq
    #
    @44
    @45
    @48
    @51
    wi
    @41
    @42
    @51
    @2
    @46
    @42
    @29
    @15
    @33
    @49
    @38
    @42
    @14
    @32
    cid
    @42
    @12
    @30
    @13
    @31
    @11
    cR
    dmeq
    @11
    cR
    rneq
    uneq12d
    reseq2d
    #
    @42
    @3
    @20
    @37
    @42
    @18
    @35
    @19
    @36
    c1
    c1
    @42
    c1
    eqidd
    @42
    vx
    vy
    cvv
    cvv
    @17
    @34
    @11
    cR
    @16
    coeq2
    mpt2eq3dv
    @42
    vz
    cvv
    @11
    cR
    @42
    id
    mpteq2dv
    seqeq123d
    #
    fveq1d
    ifeq12d
    ad2antrl
    a1i
    @41
    @43
    @47
    @2
    @41
    @41
    @46
    @42
    @9
    @3
    @3
    eqeq1
    anbi2d
    anbi2d
    @41
    @22
    @50
    @39
    @41
    @10
    @29
    @21
    @49
    @15
    @9
    @3
    cc0
    eqeq1
    @9
    @3
    @20
    fveq2
    ifbieq2d
    eqeq1d
    3imtr4d
    mpcom
    @0
    cR
    cvv
    wcel
    @1
    cR
    cV
    elex
    adantr
    #
    @2
    @3
    @2
    cN
    @0
    @1
    simpr
    #
    peano2nnd
    #
    nnnn0d
    @2
    @29
    @33
    @38
    cvv
    @0
    @33
    cvv
    wcel
    #
    @1
    @0
    @32
    cvv
    wcel
    #
    @57
    @0
    @30
    cvv
    wcel
    @31
    cvv
    wcel
    @58
    cR
    cV
    dmexg
    cR
    cV
    rnexg
    @30
    @31
    cvv
    cvv
    unexg
    syl2anc
    @32
    cvv
    resiexg
    syl
    adantr
    #
    @2
    @3
    @37
    fvexd
    ifcld
    ovmpt2d
    @2
    @29
    @33
    @38
    @2
    @3
    cn
    wcel
    #
    @29
    wn
    @56
    @60
    @3
    cc0
    @3
    nnne0
    neneqd
    syl
    iffalsed
    @2
    @38
    cN
    @37
    cfv
    #
    @3
    @36
    cfv
    #
    @35
    co
    #
    @61
    cR
    @35
    co
    #
    @26
    @2
    cN
    c1
    cuz
    cfv
    wcel
    #
    @38
    @63
    wceq
    @1
    @65
    @0
    @1
    @65
    cN
    elnnuz
    biimpi
    adantl
    @35
    @36
    c1
    cN
    seqp1
    syl
    @2
    @62
    cR
    @61
    @35
    @2
    @3
    cvv
    wcel
    @0
    @62
    cR
    wceq
    cN
    c1
    caddc
    ovex
    @0
    @1
    simpl
    #
    vz
    @3
    cR
    cR
    cvv
    cV
    @36
    vz
    cv
    @3
    wceq
    cR
    eqidd
    @36
    eqid
    fvmptg
    sylancr
    oveq2d
    @2
    @64
    @61
    cR
    va
    vb
    cvv
    cvv
    va
    cv
    #
    cR
    ccom
    #
    cmpt2
    #
    co
    #
    @61
    cR
    ccom
    #
    @26
    @35
    @69
    wceq
    @64
    @70
    wceq
    @2
    vx
    vy
    va
    vb
    cvv
    cvv
    @34
    @68
    va
    @34
    nfcv
    vb
    @34
    nfcv
    vx
    @68
    nfcv
    vy
    @68
    nfcv
    vx
    va
    weq
    #
    vy
    vb
    weq
    #
    wa
    @16
    @67
    cR
    @72
    @73
    simpl
    coeq1d
    cbvmpt2
    @61
    cR
    @35
    @69
    oveq
    mp1i
    @2
    va
    vb
    @61
    cR
    cvv
    cvv
    @68
    @71
    @69
    cvv
    @2
    @69
    eqidd
    @2
    @67
    @61
    wceq
    #
    vb
    cv
    cR
    wceq
    #
    wa
    wa
    @67
    @61
    cR
    @2
    @74
    @75
    simprl
    coeq1d
    @2
    cN
    @37
    fvexd
    #
    @54
    @2
    @61
    cvv
    wcel
    @0
    @71
    cvv
    wcel
    cN
    @37
    fvex
    @66
    @61
    cR
    cvv
    cV
    coexg
    sylancr
    ovmpt2d
    @2
    @61
    @25
    cR
    @2
    @25
    cN
    cc0
    wceq
    #
    @33
    @61
    cif
    #
    @61
    @2
    vr
    vn
    cR
    cN
    cvv
    cn0
    @22
    @78
    @23
    cvv
    @40
    @42
    @9
    cN
    wceq
    #
    wa
    #
    @22
    @78
    wceq
    @2
    @80
    @10
    @77
    @15
    @21
    @33
    @61
    @80
    @9
    cN
    cc0
    @42
    @79
    simpr
    #
    eqeq1d
    @42
    @15
    @33
    wceq
    @79
    @52
    adantr
    @80
    @9
    cN
    @20
    @37
    @42
    @20
    @37
    wceq
    @79
    @53
    adantr
    @81
    fveq12d
    ifbieq12d
    adantl
    @54
    @2
    cN
    @55
    nnnn0d
    @2
    @77
    @33
    @61
    cvv
    @59
    @76
    ifcld
    ovmpt2d
    @2
    @77
    @33
    @61
    @2
    cN
    cc0
    @1
    cN
    cc0
    wne
    @0
    cN
    nnne0
    adantl
    neneqd
    iffalsed
    eqtr2d
    coeq1d
    3eqtrd
    3eqtrd
    3eqtrd
    crelexp
    @23
    wceq
    #
    @8
    @28
    wb
    vx
    vy
    vz
    vn
    vr
    df-relexp
    @82
    @7
    @27
    @2
    @82
    @4
    @24
    @6
    @26
    cR
    @3
    crelexp
    @23
    oveq
    @82
    @5
    @25
    cR
    cR
    cN
    crelexp
    @23
    oveq
    coeq1d
    eqeq12d
    imbi2d
    ax-mp
    mpbir
end
