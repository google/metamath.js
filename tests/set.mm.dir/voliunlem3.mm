include "crn.mm"
include "cuni.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cdm.mm"
include "wcel.mm"
include "wceq.mm"
include "voliunlem2.mm"
include "mblvol.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "cv.mm"
include "ciun.mm"
include "caddc.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "eqid.mm"
include "wa.mm"
include "cr.mm"
include "wss.mm"
include "ffvelrnda.mm"
include "mblss.mm"
include "wral.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "eqeltrrd.mm"
include "ovoliun.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "fniunfv.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "seqeq3d.mm"
include "syl5req.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "3brtr3d.mm"
include "cpnf.mm"
include "wi.mm"
include "cmnf.mm"
include "cc0.mm"
include "cpw.mm"
include "frn.mm"
include "reex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "ssriv.mm"
include "syl6ss.mm"
include "sspwuni.mm"
include "sylib.mm"
include "ovolcl.mm"
include "ovolge0.mm"
include "mnflt0.mm"
include "mnfxr.mm"
include "0xr.mm"
include "xrltletr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "sylc.mm"
include "wb.mm"
include "xrrebnd.mm"
include "cdif.mm"
include "co.mm"
include "simpl.mm"
include "sseq1d.mm"
include "cin.mm"
include "simpll.mm"
include "ineq1d.mm"
include "fnfvelrn.mm"
include "elssuni.mm"
include "adantll.mm"
include "sseqin2.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "adantrr.mm"
include "3eqtr4g.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "c0.mm"
include "difeq1.mm"
include "difid.mm"
include "syl6eq.mm"
include "ovol0.mm"
include "adantr.mm"
include "oveq12d.mm"
include "nnuz.mm"
include "1zzd.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "serfre.mm"
include "feq1i.mm"
include "recnd.mm"
include "addid1d.mm"
include "breq12d.mm"
include "expr.mm"
include "pm5.74d.mm"
include "imbi12d.mm"
include "pm5.74da.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "wdisj.mm"
include "simp2.mm"
include "simp3.mm"
include "voliunlem1.mm"
include "3exp1.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "mpd.mm"
include "sylbird.mm"
include "mpand.mm"
include "wn.mm"
include "nltpnft.mm"
include "rexr.mm"
include "pnfge.mm"
include "3syl.mm"
include "ex.mm"
include "breq2.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "pm2.61d.mm"
include "ralrimiv.mm"
include "breq1.mm"
include "ralrn.mm"
include "mpbird.mm"
include "ressxr.mm"
include "supxrleub.mm"
include "syl2anc.mm"
include "supxrcl.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem voliunlem3
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let vk: setvar k
  let vz: setvar z
  let cE: class E
  assume voliunlem.3: |- ( ph -> F : NN --> dom vol )
  assume voliunlem.5: |- ( ph -> Disj_ i e. NN ( F ` i ) )
  assume voliunlem.6: |- H = ( n e. NN |-> ( vol* ` ( x i^i ( F ` n ) ) ) )
  assume voliunlem3.1: |- S = seq 1 ( + , G )
  assume voliunlem3.2: |- G = ( n e. NN |-> ( vol ` ( F ` n ) ) )
  assume voliunlem3.4: |- ( ph -> A. i e. NN ( vol ` ( F ` i ) ) e. RR )

  disjoint i n
  disjoint i x
  disjoint F i
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint S x
  disjoint n ph
  disjoint ph x
  disjoint k n
  disjoint k z
  disjoint E k
  disjoint n z
  disjoint E n
  disjoint E z
  disjoint i k
  disjoint i z
  disjoint k x
  disjoint F k
  disjoint x z
  disjoint F z
  disjoint G k
  disjoint H k
  disjoint H z
  disjoint S k
  disjoint S z
  disjoint k ph
  disjoint ph z
  assert |- ( ph -> ( vol ` U. ran F ) = sup ( ran S , RR* , < ) )

  proof
    wph
    cF
    crn
    #
    cuni
    #
    cvol
    cfv
    #
    @1
    covol
    cfv
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    wph
    @1
    cvol
    cdm
    #
    wcel
    @2
    @3
    wceq
    wph
    vx
    vi
    vn
    cF
    cH
    voliunlem.3
    voliunlem.5
    voliunlem.6
    voliunlem2
    @1
    mblvol
    syl
    wph
    @3
    @5
    wceq
    #
    @3
    @5
    cle
    wbr
    #
    @5
    @3
    cle
    wbr
    #
    wph
    vn
    cn
    vn
    cv
    #
    cF
    cfv
    #
    ciun
    #
    covol
    cfv
    caddc
    vn
    cn
    @11
    covol
    cfv
    #
    cmpt
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    @3
    @5
    cle
    wph
    @11
    @15
    vn
    @14
    @15
    eqid
    @14
    eqid
    wph
    @10
    cn
    wcel
    #
    wa
    #
    @11
    @6
    wcel
    #
    @11
    cr
    wss
    wph
    cn
    @6
    @10
    cF
    voliunlem.3
    ffvelrnda
    #
    @11
    mblss
    syl
    @18
    @11
    cvol
    cfv
    #
    @13
    cr
    @18
    @19
    @21
    @13
    wceq
    #
    @20
    @11
    mblvol
    syl
    #
    wph
    vi
    cv
    #
    cF
    cfv
    #
    cvol
    cfv
    #
    cr
    wcel
    #
    vi
    cn
    wral
    #
    @17
    @21
    cr
    wcel
    #
    voliunlem3.4
    @27
    @29
    vi
    @10
    cn
    vi
    vn
    weq
    #
    @26
    @21
    cr
    @30
    @25
    @11
    cvol
    @24
    @10
    cF
    fveq2
    fveq2d
    eleq1d
    rspccva
    sylan
    eqeltrrd
    ovoliun
    wph
    @12
    @1
    covol
    wph
    cF
    cn
    wfn
    #
    @12
    @1
    wceq
    wph
    cn
    @6
    cF
    wf
    #
    @31
    voliunlem.3
    cn
    @6
    cF
    ffn
    syl
    #
    vn
    cn
    cF
    fniunfv
    syl
    fveq2d
    wph
    cxr
    @16
    @4
    clt
    wph
    @15
    cS
    wph
    cS
    caddc
    cG
    c1
    cseq
    #
    @15
    voliunlem3.1
    wph
    cG
    @14
    caddc
    c1
    wph
    cG
    vn
    cn
    @21
    cmpt
    #
    @14
    voliunlem3.2
    wph
    vn
    cn
    @21
    @13
    @23
    mpteq2dva
    syl5eq
    seqeq3d
    syl5req
    rneqd
    supeq1d
    3brtr3d
    wph
    @9
    vz
    cv
    #
    @3
    cle
    wbr
    #
    vz
    @4
    wral
    #
    wph
    @38
    vk
    cv
    #
    cS
    cfv
    #
    @3
    cle
    wbr
    #
    vk
    cn
    wral
    #
    wph
    @41
    vk
    cn
    wph
    @3
    cpnf
    clt
    wbr
    #
    @39
    cn
    wcel
    #
    @41
    wi
    #
    wph
    cmnf
    @3
    clt
    wbr
    #
    @43
    @45
    wph
    @3
    cxr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @46
    wph
    @1
    cr
    wss
    #
    @47
    wph
    @0
    cr
    cpw
    #
    wss
    @49
    wph
    @0
    @6
    @50
    wph
    @32
    @0
    @6
    wss
    voliunlem.3
    cn
    @6
    cF
    frn
    syl
    vx
    @6
    @50
    vx
    cv
    #
    @6
    wcel
    @51
    cr
    wss
    #
    @51
    @50
    wcel
    @51
    mblss
    @51
    cr
    reex
    elpw2
    sylibr
    ssriv
    syl6ss
    @0
    cr
    sspwuni
    sylib
    #
    @1
    ovolcl
    syl
    #
    wph
    @49
    @48
    @53
    @1
    ovolge0
    syl
    @47
    cmnf
    cc0
    clt
    wbr
    #
    @48
    @46
    mnflt0
    cmnf
    cxr
    wcel
    cc0
    cxr
    wcel
    @47
    @55
    @48
    wa
    @46
    wi
    mnfxr
    0xr
    cmnf
    cc0
    @3
    xrltletr
    mp3an12
    mpani
    sylc
    wph
    @46
    @43
    wa
    #
    @3
    cr
    wcel
    #
    @45
    wph
    @47
    @57
    @56
    wb
    @54
    @3
    xrrebnd
    syl
    wph
    @49
    @57
    @45
    wi
    #
    @53
    @1
    @50
    wcel
    #
    wph
    @49
    @58
    wi
    #
    wph
    @49
    @59
    @53
    @1
    cr
    reex
    elpw2
    sylibr
    wph
    @52
    @51
    covol
    cfv
    #
    cr
    wcel
    #
    @44
    @39
    caddc
    cH
    c1
    cseq
    #
    cfv
    #
    @51
    @1
    cdif
    #
    covol
    cfv
    #
    caddc
    co
    #
    @61
    cle
    wbr
    #
    wi
    #
    wi
    #
    wi
    #
    wi
    wph
    @60
    wi
    vx
    @1
    @50
    @51
    @1
    wceq
    #
    wph
    @71
    @60
    @72
    wph
    wa
    #
    @52
    @49
    @70
    @58
    @73
    @51
    @1
    cr
    @72
    wph
    simpl
    #
    sseq1d
    @73
    @62
    @57
    @69
    @45
    @73
    @61
    @3
    cr
    @73
    @51
    @1
    covol
    @74
    fveq2d
    eleq1d
    @73
    @44
    @68
    @41
    @72
    wph
    @44
    @68
    @41
    wb
    @72
    wph
    @44
    wa
    #
    wa
    #
    @67
    @40
    @61
    @3
    cle
    @76
    @67
    @40
    cc0
    caddc
    co
    @40
    @76
    @64
    @40
    @66
    cc0
    caddc
    @76
    @39
    @63
    cS
    @76
    @63
    @34
    cS
    @76
    cH
    cG
    caddc
    c1
    @76
    vn
    cn
    @51
    @11
    cin
    #
    covol
    cfv
    #
    cmpt
    #
    @35
    cH
    cG
    @72
    wph
    @79
    @35
    wceq
    @44
    @73
    vn
    cn
    @78
    @21
    @73
    @17
    wa
    #
    @78
    @13
    @21
    @80
    @77
    @11
    covol
    @80
    @77
    @1
    @11
    cin
    #
    @11
    @80
    @51
    @1
    @11
    @72
    wph
    @17
    simpll
    ineq1d
    @80
    @11
    @1
    wss
    #
    @81
    @11
    wceq
    wph
    @17
    @82
    @72
    @18
    @11
    @0
    wcel
    #
    @82
    wph
    @31
    @17
    @83
    @33
    cn
    @10
    cF
    fnfvelrn
    sylan
    @11
    @0
    elssuni
    syl
    adantll
    @11
    @1
    sseqin2
    sylib
    eqtrd
    fveq2d
    wph
    @17
    @22
    @72
    @23
    adantll
    eqtr4d
    mpteq2dva
    adantrr
    voliunlem.6
    voliunlem3.2
    3eqtr4g
    seqeq3d
    voliunlem3.1
    syl6eqr
    fveq1d
    @72
    @66
    cc0
    wceq
    @75
    @72
    @66
    c0
    covol
    cfv
    cc0
    @72
    @65
    c0
    covol
    @72
    @65
    @1
    @1
    cdif
    c0
    @51
    @1
    @1
    difeq1
    @1
    difid
    syl6eq
    fveq2d
    ovol0
    syl6eq
    adantr
    oveq12d
    @76
    @40
    @76
    @40
    @75
    @40
    cr
    wcel
    #
    @72
    wph
    cn
    cr
    @39
    cS
    wph
    cn
    cr
    @34
    wf
    cn
    cr
    cS
    wf
    #
    wph
    vk
    cG
    c1
    cn
    nnuz
    wph
    1zzd
    @75
    @39
    cG
    cfv
    #
    @39
    cF
    cfv
    #
    cvol
    cfv
    #
    cr
    @44
    @86
    @88
    wceq
    wph
    vn
    @39
    @21
    @88
    cn
    cG
    vn
    vk
    weq
    @11
    @87
    cvol
    @10
    @39
    cF
    fveq2
    fveq2d
    voliunlem3.2
    @87
    cvol
    fvex
    fvmpt
    adantl
    wph
    @28
    @44
    @88
    cr
    wcel
    #
    voliunlem3.4
    @27
    @89
    vi
    @39
    cn
    vi
    vk
    weq
    #
    @26
    @88
    cr
    @90
    @25
    @87
    cvol
    @24
    @39
    cF
    fveq2
    fveq2d
    eleq1d
    rspccva
    sylan
    eqeltrd
    serfre
    cn
    cr
    cS
    @34
    voliunlem3.1
    feq1i
    sylibr
    #
    ffvelrnda
    #
    adantl
    recnd
    addid1d
    eqtrd
    @72
    @61
    @3
    wceq
    @75
    @51
    @1
    covol
    fveq2
    adantr
    breq12d
    expr
    pm5.74d
    imbi12d
    imbi12d
    pm5.74da
    wph
    @52
    @62
    @44
    @68
    wph
    @52
    @62
    w3a
    vi
    vk
    vn
    @51
    cF
    cH
    wph
    @52
    @32
    @62
    voliunlem.3
    3ad2ant1
    wph
    @52
    vi
    cn
    @25
    wdisj
    @62
    voliunlem.5
    3ad2ant1
    voliunlem.6
    wph
    @52
    @62
    simp2
    wph
    @52
    @62
    simp3
    voliunlem1
    3exp1
    vtoclg
    mpcom
    mpd
    sylbird
    mpand
    wph
    @43
    wn
    #
    @3
    cpnf
    wceq
    #
    @45
    wph
    @47
    @94
    @93
    wb
    @54
    @3
    nltpnft
    syl
    wph
    @45
    @94
    @44
    @40
    cpnf
    cle
    wbr
    #
    wi
    wph
    @44
    @95
    @75
    @84
    @40
    cxr
    wcel
    @95
    @92
    @40
    rexr
    @40
    pnfge
    3syl
    ex
    @94
    @41
    @95
    @44
    @3
    cpnf
    @40
    cle
    breq2
    imbi2d
    syl5ibrcom
    sylbird
    pm2.61d
    ralrimiv
    wph
    cS
    cn
    wfn
    #
    @38
    @42
    wb
    wph
    @85
    @96
    @91
    cn
    cr
    cS
    ffn
    syl
    @37
    @41
    vz
    vk
    cn
    cS
    @36
    @40
    @3
    cle
    breq1
    ralrn
    syl
    mpbird
    wph
    @4
    cxr
    wss
    #
    @47
    @9
    @38
    wb
    wph
    @4
    cr
    cxr
    wph
    @85
    @4
    cr
    wss
    @91
    cn
    cr
    cS
    frn
    syl
    ressxr
    syl6ss
    #
    @54
    vz
    @4
    @3
    supxrleub
    syl2anc
    mpbird
    wph
    @47
    @5
    cxr
    wcel
    #
    @7
    @8
    @9
    wa
    wb
    @54
    wph
    @97
    @99
    @98
    @4
    supxrcl
    syl
    @3
    @5
    xrletri3
    syl2anc
    mpbir2and
    eqtrd
end
