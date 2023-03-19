include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "wcel.mm"
include "ctopn.mm"
include "cmopn.mm"
include "wceq.mm"
include "cxme.mm"
include "wss.mm"
include "eqid.mm"
include "xmsxmet.mm"
include "syl.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "fveq2d.mm"
include "3eltr4d.mm"
include "imasf1oxmet.mm"
include "wf1o.mm"
include "wfo.mm"
include "f1ofo.mm"
include "imasbas.mm"
include "eleqtrd.mm"
include "ssid.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "cqtop.mm"
include "co.mm"
include "imastopn.mm"
include "xmstopn.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "cbl.mm"
include "crn.mm"
include "ctg.mm"
include "ctb.mm"
include "cuni.mm"
include "blbas.mm"
include "wb.mm"
include "unirnbl.mm"
include "f1oeq2.mm"
include "3syl.mm"
include "mpbird.mm"
include "tgqtop.mm"
include "syl2anc.mm"
include "mopnval.mm"
include "cxr.mm"
include "wf.mm"
include "wfn.mm"
include "xmetf.mm"
include "ffn.mm"
include "fnresdm.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wa.mm"
include "wrex.mm"
include "wf1.mm"
include "ad2antrr.mm"
include "f1of1.mm"
include "cdm.mm"
include "cnvimass.mm"
include "f1odm.mm"
include "syl5sseq.mm"
include "simprl.mm"
include "simprr.mm"
include "blssm.mm"
include "syl3anc.mm"
include "f1imaeq.mm"
include "syl12anc.mm"
include "simplr.mm"
include "foimacnv.mm"
include "cimas.mm"
include "imasf1obl.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "bitr3d.mm"
include "2rexbidva.mm"
include "adantr.mm"
include "f1ofn.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "rexrn.mm"
include "forn.mm"
include "rexeqdv.mm"
include "3bitr2d.mm"
include "blrn.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "elqtop2.mm"
include "cpw.mm"
include "blf.mm"
include "frn.mm"
include "sseld.mm"
include "elpwi.mm"
include "syl6.mm"
include "pm4.71rd.mm"
include "eqrdv.mm"
include "3eqtr4d.mm"
include "3eqtrd.mm"
include "isxms2.mm"
include "sylanbrc.mm"

theorem imasf1oxms
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let cD: class D
  let vx: setvar x
  let cE: class E
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  assume imasf1obl.u: |- ( ph -> U = ( F "s R ) )
  assume imasf1obl.v: |- ( ph -> V = ( Base ` R ) )
  assume imasf1obl.f: |- ( ph -> F : V -1-1-onto-> B )
  assume imasf1oxms.r: |- ( ph -> R e. *MetSp )


  assert |- ( ph -> U e. *MetSp )

  proof
    wph
    cU
    cds
    cfv
    #
    cU
    cbs
    cfv
    #
    @1
    cxp
    #
    cres
    #
    @1
    cxmt
    cfv
    #
    wcel
    #
    cU
    ctopn
    cfv
    #
    @3
    cmopn
    cfv
    #
    wceq
    cU
    cxme
    wcel
    wph
    @0
    @4
    wcel
    #
    @1
    @1
    wss
    @5
    wph
    @0
    cB
    cxmt
    cfv
    #
    @4
    wph
    cB
    @0
    cR
    cU
    cR
    cds
    cfv
    #
    cV
    cV
    cxp
    #
    cres
    #
    cF
    cV
    cxme
    imasf1obl.u
    imasf1obl.v
    imasf1obl.f
    imasf1oxms.r
    @12
    eqid
    #
    @0
    eqid
    #
    wph
    @10
    cR
    cbs
    cfv
    #
    @15
    cxp
    #
    cres
    #
    @15
    cxmt
    cfv
    #
    @12
    cV
    cxmt
    cfv
    #
    wph
    cR
    cxme
    wcel
    #
    @17
    @18
    wcel
    imasf1oxms.r
    @17
    cR
    @15
    @15
    eqid
    #
    @17
    eqid
    #
    xmsxmet
    syl
    wph
    @11
    @16
    @10
    wph
    cV
    @15
    imasf1obl.v
    sqxpeqd
    reseq2d
    #
    wph
    cV
    @15
    cxmt
    imasf1obl.v
    fveq2d
    3eltr4d
    #
    imasf1oxmet
    #
    wph
    cB
    @1
    cxmt
    wph
    cB
    cR
    cU
    cF
    cV
    cxme
    imasf1obl.u
    imasf1obl.v
    wph
    cV
    cB
    cF
    wf1o
    #
    cV
    cB
    cF
    wfo
    #
    imasf1obl.f
    cV
    cB
    cF
    f1ofo
    #
    syl
    #
    imasf1oxms.r
    imasbas
    fveq2d
    eleqtrd
    #
    @1
    ssid
    @0
    @1
    @1
    xmetres2
    sylancl
    wph
    @6
    cR
    ctopn
    cfv
    #
    cF
    cqtop
    co
    @12
    cmopn
    cfv
    #
    cF
    cqtop
    co
    #
    @7
    wph
    cB
    cR
    cU
    cF
    @31
    @6
    cV
    cxme
    imasf1obl.u
    imasf1obl.v
    @29
    imasf1oxms.r
    @31
    eqid
    #
    @6
    eqid
    #
    imastopn
    wph
    @31
    @32
    cF
    cqtop
    wph
    @31
    @17
    cmopn
    cfv
    #
    @32
    wph
    @20
    @31
    @36
    wceq
    imasf1oxms.r
    @17
    @31
    cR
    @15
    @34
    @21
    @22
    xmstopn
    syl
    wph
    @12
    @17
    cmopn
    @23
    fveq2d
    eqtr4d
    oveq1d
    wph
    @12
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    #
    cF
    cqtop
    co
    #
    @38
    cF
    cqtop
    co
    #
    ctg
    cfv
    #
    @33
    @7
    wph
    @38
    ctb
    wcel
    #
    @38
    cuni
    #
    cB
    cF
    wf1o
    #
    @40
    @42
    wceq
    wph
    @12
    @19
    wcel
    #
    @43
    @24
    @12
    cV
    blbas
    syl
    #
    wph
    @45
    @26
    imasf1obl.f
    wph
    @46
    @44
    cV
    wceq
    @45
    @26
    wb
    @24
    @12
    cV
    unirnbl
    @44
    cV
    cB
    cF
    f1oeq2
    3syl
    mpbird
    #
    cF
    @38
    @44
    cB
    @44
    eqid
    #
    tgqtop
    syl2anc
    wph
    @32
    @39
    cF
    cqtop
    wph
    @46
    @32
    @39
    wceq
    @24
    @12
    @32
    cV
    @32
    eqid
    mopnval
    syl
    oveq1d
    wph
    @0
    cmopn
    cfv
    #
    @0
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    #
    @7
    @42
    wph
    @0
    @9
    wcel
    #
    @50
    @53
    wceq
    @25
    @0
    @50
    cB
    @50
    eqid
    mopnval
    syl
    wph
    @3
    @0
    cmopn
    wph
    @2
    cxr
    @0
    wf
    #
    @0
    @2
    wfn
    @3
    @0
    wceq
    wph
    @8
    @55
    @30
    @0
    @1
    xmetf
    syl
    @2
    cxr
    @0
    ffn
    @2
    @0
    fnresdm
    3syl
    fveq2d
    wph
    @41
    @52
    ctg
    wph
    vx
    @41
    @52
    wph
    vx
    cv
    #
    cB
    wss
    #
    cF
    ccnv
    @56
    cima
    #
    @38
    wcel
    #
    wa
    #
    @57
    @56
    @52
    wcel
    #
    wa
    @56
    @41
    wcel
    #
    @61
    wph
    @57
    @59
    @61
    wph
    @57
    wa
    #
    @58
    vy
    cv
    #
    vr
    cv
    #
    @37
    co
    #
    wceq
    #
    vr
    cxr
    wrex
    vy
    cV
    wrex
    #
    @56
    vz
    cv
    #
    @65
    @51
    co
    #
    wceq
    #
    vr
    cxr
    wrex
    #
    vz
    cB
    wrex
    #
    @59
    @61
    @63
    @68
    @56
    @64
    cF
    cfv
    #
    @65
    @51
    co
    #
    wceq
    #
    vr
    cxr
    wrex
    #
    vy
    cV
    wrex
    #
    @72
    vz
    cF
    crn
    #
    wrex
    #
    @73
    @63
    @67
    @76
    vy
    vr
    cV
    cxr
    @63
    @64
    cV
    wcel
    #
    @65
    cxr
    wcel
    #
    wa
    #
    wa
    #
    cF
    @58
    cima
    #
    cF
    @66
    cima
    #
    wceq
    #
    @67
    @76
    @84
    cV
    cB
    cF
    wf1
    #
    @58
    cV
    wss
    @66
    cV
    wss
    #
    @87
    @67
    wb
    @84
    @26
    @88
    wph
    @26
    @57
    @83
    imasf1obl.f
    ad2antrr
    #
    cV
    cB
    cF
    f1of1
    syl
    @84
    cF
    cdm
    #
    @58
    cV
    cF
    @56
    cnvimass
    @84
    @26
    @91
    cV
    wceq
    @90
    cV
    cB
    cF
    f1odm
    syl
    syl5sseq
    @84
    @46
    @81
    @82
    @89
    wph
    @46
    @57
    @83
    @24
    ad2antrr
    #
    @63
    @81
    @82
    simprl
    #
    @63
    @81
    @82
    simprr
    #
    @12
    @64
    @65
    cV
    blssm
    syl3anc
    cV
    cB
    @58
    @66
    cF
    f1imaeq
    syl12anc
    @84
    @85
    @56
    @86
    @75
    @84
    @27
    @57
    @85
    @56
    wceq
    @84
    @26
    @27
    @90
    @28
    syl
    wph
    @57
    @83
    simplr
    cV
    cB
    @56
    cF
    foimacnv
    syl2anc
    @84
    @75
    @86
    @84
    cB
    @0
    @64
    cR
    @65
    cU
    @12
    cF
    cV
    cxme
    wph
    cU
    cF
    cR
    cimas
    co
    wceq
    @57
    @83
    imasf1obl.u
    ad2antrr
    wph
    cV
    @15
    wceq
    @57
    @83
    imasf1obl.v
    ad2antrr
    @90
    wph
    @20
    @57
    @83
    imasf1oxms.r
    ad2antrr
    @13
    @14
    @92
    @93
    @94
    imasf1obl
    eqcomd
    eqeq12d
    bitr3d
    2rexbidva
    @63
    @26
    cF
    cV
    wfn
    @80
    @78
    wb
    wph
    @26
    @57
    imasf1obl.f
    adantr
    #
    cV
    cB
    cF
    f1ofn
    @72
    @77
    vz
    vy
    cV
    cF
    @69
    @74
    wceq
    #
    @71
    @76
    vr
    cxr
    @96
    @70
    @75
    @56
    @69
    @74
    @65
    @51
    oveq1
    eqeq2d
    rexbidv
    rexrn
    3syl
    @63
    @72
    vz
    @79
    cB
    @63
    @26
    @27
    @79
    cB
    wceq
    @95
    @28
    cV
    cB
    cF
    forn
    3syl
    rexeqdv
    3bitr2d
    @63
    @46
    @59
    @68
    wb
    wph
    @46
    @57
    @24
    adantr
    vy
    @58
    @12
    cV
    vr
    blrn
    syl
    @63
    @54
    @61
    @73
    wb
    wph
    @54
    @57
    @25
    adantr
    vz
    @56
    @0
    cB
    vr
    blrn
    syl
    3bitr4d
    pm5.32da
    wph
    @43
    @44
    cB
    cF
    wfo
    #
    @62
    @60
    wb
    @47
    wph
    @45
    @97
    @48
    @44
    cB
    cF
    f1ofo
    syl
    @56
    cF
    @38
    ctb
    @44
    cB
    @49
    elqtop2
    syl2anc
    wph
    @61
    @57
    wph
    @61
    @56
    cB
    cpw
    #
    wcel
    @57
    wph
    @52
    @98
    @56
    wph
    @54
    cB
    cxr
    cxp
    #
    @98
    @51
    wf
    @52
    @98
    wss
    @25
    @0
    cB
    blf
    @99
    @98
    @51
    frn
    3syl
    sseld
    @56
    cB
    elpwi
    syl6
    pm4.71rd
    3bitr4d
    eqrdv
    fveq2d
    3eqtr4d
    3eqtr4d
    3eqtrd
    @3
    @6
    cU
    @1
    @35
    @1
    eqid
    @3
    eqid
    isxms2
    sylanbrc
end
