include "wcel.mm"
include "ces.mm"
include "co.mm"
include "cfv.mm"
include "crn.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "ccrg.mm"
include "csubrg.mm"
include "w3a.mm"
include "ne0i.mm"
include "eleq2s.mm"
include "wceq.mm"
include "rneq.mm"
include "rn0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "wa.mm"
include "fveq1.mm"
include "0fv.mm"
include "reldmevls.mm"
include "ovprc1.mm"
include "necon1ai.mm"
include "cv.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "cbs.mm"
include "cress.mm"
include "cmpl.mm"
include "cascl.mm"
include "ccom.mm"
include "cmap.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cmvr.mm"
include "cpws.mm"
include "crh.mm"
include "crio.mm"
include "csb.mm"
include "df-evls.mm"
include "elmpt2cl2.mm"
include "a1d.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "jcai.mm"
include "syl.mm"
include "wn.mm"
include "cdm.mm"
include "fvex.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfmpt.mm"
include "csbeq1a.mm"
include "mpteq2dv.mm"
include "csbief.mm"
include "fveq2.mm"
include "adantl.mm"
include "csbeq1d.mm"
include "id.mm"
include "oveq1.mm"
include "oveqan12d.mm"
include "oveq2.mm"
include "oveqan12rd.mm"
include "oveq2d.mm"
include "adantr.mm"
include "xpeq1d.mm"
include "eqeq2d.mm"
include "coeq2d.mm"
include "simpl.mm"
include "mpteq1d.mm"
include "mpteq12dv.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "riotaeqbidv.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "dmeqd.mm"
include "eqid.mm"
include "dmmptss.mm"
include "syl6eqss.mm"
include "ssneld.mm"
include "ndmfv.mm"
include "syl6.mm"
include "necon1ad.mm"
include "com12.mm"
include "df-3an.mm"
include "sylibr.mm"
include "3syl.mm"

theorem mpfrcl
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cI: class I
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  assume mpfrcl.q: |- Q = ran ( ( I evalSub S ) ` R )


  assert |- ( X e. Q -> ( I e. _V /\ S e. CRing /\ R e. ( SubRing ` S ) ) )

  proof
    cX
    cQ
    wcel
    cR
    cI
    cS
    ces
    co
    #
    cfv
    #
    crn
    #
    c0
    wne
    #
    @1
    c0
    wne
    #
    cI
    cvv
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    #
    wcel
    #
    w3a
    #
    @3
    cX
    @2
    cQ
    @2
    cX
    ne0i
    mpfrcl.q
    eleq2s
    @1
    c0
    @2
    c0
    @1
    c0
    wceq
    #
    @2
    c0
    crn
    c0
    @1
    c0
    rneq
    rn0
    syl6eq
    necon3i
    @4
    @5
    @6
    wa
    #
    @8
    wa
    @9
    @4
    @11
    @8
    @4
    @0
    c0
    wne
    #
    @11
    @0
    c0
    @1
    c0
    @0
    c0
    wceq
    @1
    cR
    c0
    cfv
    c0
    cR
    @0
    c0
    fveq1
    cR
    0fv
    syl6eq
    necon3i
    @12
    @5
    @6
    @5
    @0
    c0
    cI
    cS
    ces
    reldmevls
    ovprc1
    necon1ai
    @12
    va
    cv
    #
    @0
    wcel
    #
    va
    wex
    @5
    @6
    wi
    #
    va
    @0
    n0
    @14
    @15
    va
    @14
    @6
    @5
    vi
    vs
    cvv
    ccrg
    vb
    vs
    cv
    #
    cbs
    cfv
    #
    vr
    @16
    csubrg
    cfv
    #
    vw
    vi
    cv
    #
    @16
    vr
    cv
    #
    cress
    co
    #
    cmpl
    co
    #
    vf
    cv
    #
    vw
    cv
    #
    cascl
    cfv
    ccom
    #
    vx
    @20
    vb
    cv
    #
    @19
    cmap
    co
    #
    vx
    cv
    #
    csn
    #
    cxp
    #
    cmpt
    #
    wceq
    #
    @23
    @19
    @21
    cmvr
    co
    #
    ccom
    #
    vx
    @19
    vg
    @27
    @28
    vg
    cv
    cfv
    #
    cmpt
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vf
    @24
    @16
    @27
    cpws
    co
    #
    crh
    co
    #
    crio
    #
    csb
    #
    cmpt
    #
    csb
    #
    cI
    cS
    ces
    @13
    vx
    vw
    vf
    vg
    vi
    vs
    vr
    vb
    df-evls
    #
    elmpt2cl2
    a1d
    exlimiv
    sylbi
    jcai
    syl
    @11
    @4
    @8
    @11
    @8
    @1
    c0
    @11
    @8
    wn
    cR
    @0
    cdm
    #
    wcel
    wn
    @10
    @11
    @47
    @7
    cR
    @11
    @47
    vr
    @7
    vb
    cS
    cbs
    cfv
    #
    vw
    cI
    cS
    @20
    cress
    co
    #
    cmpl
    co
    #
    @25
    vx
    @20
    @26
    cI
    cmap
    co
    #
    @29
    cxp
    #
    cmpt
    #
    wceq
    #
    @23
    cI
    @49
    cmvr
    co
    #
    ccom
    #
    vx
    cI
    vg
    @51
    @35
    cmpt
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vf
    @24
    cS
    @51
    cpws
    co
    #
    crh
    co
    #
    crio
    #
    csb
    #
    csb
    #
    cmpt
    #
    cdm
    @7
    @11
    @0
    @66
    vi
    vs
    cI
    cS
    cvv
    ccrg
    @45
    @66
    ces
    @19
    cI
    wceq
    #
    @16
    cS
    wceq
    #
    wa
    #
    @45
    vr
    @18
    vb
    @17
    @43
    csb
    #
    cmpt
    #
    @66
    vb
    @17
    @44
    @71
    @16
    cbs
    fvex
    vb
    vr
    @18
    @70
    vb
    @18
    nfcv
    vb
    @17
    @43
    nfcsb1v
    nfmpt
    @26
    @17
    wceq
    vr
    @18
    @43
    @70
    vb
    @17
    @43
    csbeq1a
    mpteq2dv
    csbief
    @69
    vr
    @18
    @70
    @7
    @65
    @68
    @18
    @7
    wceq
    @67
    @16
    cS
    csubrg
    fveq2
    adantl
    @69
    @70
    vb
    @48
    @43
    csb
    @65
    @69
    vb
    @17
    @48
    @43
    @68
    @17
    @48
    wceq
    @67
    @16
    cS
    cbs
    fveq2
    adantl
    csbeq1d
    @69
    vb
    @48
    @43
    @64
    @69
    @43
    vw
    @50
    @42
    csb
    @64
    @69
    vw
    @22
    @50
    @42
    @67
    @68
    @19
    cI
    @21
    @49
    cmpl
    @67
    id
    #
    @16
    cS
    @20
    cress
    oveq1
    #
    oveqan12d
    csbeq1d
    @69
    vw
    @50
    @42
    @63
    @69
    @39
    @60
    vf
    @41
    @62
    @69
    @40
    @61
    @24
    crh
    @68
    @67
    @16
    cS
    @27
    @51
    cpws
    @68
    id
    @19
    cI
    @26
    cmap
    oveq2
    #
    oveqan12rd
    oveq2d
    @69
    @32
    @54
    @38
    @59
    @69
    @31
    @53
    @25
    @69
    vx
    @20
    @30
    @52
    @69
    @27
    @51
    @29
    @67
    @27
    @51
    wceq
    @68
    @74
    adantr
    #
    xpeq1d
    mpteq2dv
    eqeq2d
    @69
    @34
    @56
    @37
    @58
    @69
    @33
    @55
    @23
    @67
    @68
    @19
    cI
    @21
    @49
    cmvr
    @72
    @73
    oveqan12d
    coeq2d
    @69
    vx
    @19
    @36
    cI
    @57
    @67
    @68
    simpl
    @69
    vg
    @27
    @51
    @35
    @75
    mpteq1d
    mpteq12dv
    eqeq12d
    anbi12d
    riotaeqbidv
    csbeq2dv
    eqtrd
    csbeq2dv
    eqtrd
    mpteq12dv
    syl5eq
    @46
    vr
    @7
    @65
    cS
    csubrg
    fvex
    mptex
    ovmpt2a
    dmeqd
    vr
    @7
    @65
    @66
    @66
    eqid
    dmmptss
    syl6eqss
    ssneld
    cR
    @0
    ndmfv
    syl6
    necon1ad
    com12
    jcai
    @5
    @6
    @8
    df-3an
    sylibr
    3syl
end
