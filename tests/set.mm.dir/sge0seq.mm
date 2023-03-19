include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csumge0.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wceq.mm"
include "wf.mm"
include "caddc.mm"
include "cseq.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "rge0ssre.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "readdcl.mm"
include "adantl.mm"
include "seqf.mm"
include "a1i.mm"
include "feq1d.mm"
include "mpbird.mm"
include "frn.mm"
include "syl.mm"
include "ressxr.mm"
include "sstrd.mm"
include "cvv.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cicc.mm"
include "icossicc.mm"
include "fssd.mm"
include "sge0xrcl.mm"
include "simpr.mm"
include "wb.mm"
include "wfn.mm"
include "ffn.mm"
include "fvelrnb.mm"
include "adantr.mm"
include "mpbid.mm"
include "w3a.mm"
include "cfz.mm"
include "cmpt.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "ssriv.mm"
include "sge0lessmpt.mm"
include "3ad2ant1.mm"
include "csu.mm"
include "fzfid.mm"
include "sylan2.mm"
include "sge0fsummpt.mm"
include "simpll.mm"
include "eqidd.mm"
include "syl2anc.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "cc.mm"
include "recnd.mm"
include "fsumser.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "eqcomi.mm"
include "fveq1i.mm"
include "simp3.mm"
include "3eqtrrd.mm"
include "feqmptd.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "nfv.mm"
include "ad4ant14.mm"
include "simplr.mm"
include "breqtrd.mm"
include "adantlr.mm"
include "sge0gtfsumgt.mm"
include "cz.mm"
include "elpwinss.mm"
include "3ad2ant2.mm"
include "elinel2.mm"
include "uzfissfz.mm"
include "3adant1r.mm"
include "simpl1r.mm"
include "fmpt3d.mm"
include "ad2antrr.mm"
include "sselda.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "fsumrecl.mm"
include "ad4ant13.mm"
include "3adantl3.mm"
include "ad3antrrr.mm"
include "simpl3.mm"
include "0xr.mm"
include "pnfxr.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "fsumless.mm"
include "3ad2antl1.mm"
include "ltletrd.mm"
include "ex.mm"
include "reximdv.mm"
include "ffnd.mm"
include "sylibr.mm"
include "fnfvelrn.mm"
include "rneqd.mm"
include "eleq12d.mm"
include "breq2.mm"
include "rspcev.mm"
include "supxr2.mm"
include "syl22anc.mm"
include "eqcomd.mm"

theorem sge0seq
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vk: setvar k
  let vj: setvar j
  let vw: setvar w
  let vz: setvar z
  let vy: setvar y
  let vx: setvar x
  assume sge0seq.m: |- ( ph -> M e. ZZ )
  assume sge0seq.z: |- Z = ( ZZ>= ` M )
  assume sge0seq.f: |- ( ph -> F : Z --> ( 0 [,) +oo ) )
  assume sge0seq.g: |- G = seq M ( + , F )


  assert |- ( ph -> ( sum^ ` F ) = sup ( ran G , RR* , < ) )

  proof
    wph
    cG
    crn
    #
    cxr
    clt
    csup
    #
    cF
    csumge0
    cfv
    #
    wph
    @0
    cxr
    wss
    @2
    cxr
    wcel
    vz
    cv
    #
    @2
    cle
    wbr
    #
    vz
    @0
    wral
    @3
    @2
    clt
    wbr
    #
    @3
    vy
    cv
    #
    clt
    wbr
    #
    vy
    @0
    wrex
    #
    wi
    #
    vz
    cr
    wral
    @1
    @2
    wceq
    wph
    @0
    cr
    cxr
    wph
    cZ
    cr
    cG
    wf
    #
    @0
    cr
    wss
    wph
    @10
    cZ
    cr
    caddc
    cF
    cM
    cseq
    #
    wf
    wph
    vk
    vi
    caddc
    cr
    cF
    cM
    cZ
    sge0seq.z
    sge0seq.m
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    @12
    cF
    cfv
    #
    rge0ssre
    wph
    cZ
    @15
    @12
    cF
    sge0seq.f
    ffvelrnda
    #
    sseldi
    #
    @12
    cr
    wcel
    vi
    cv
    #
    cr
    wcel
    wa
    @12
    @19
    caddc
    co
    cr
    wcel
    wph
    @12
    @19
    readdcl
    adantl
    seqf
    #
    wph
    cZ
    cr
    cG
    @11
    cG
    @11
    wceq
    #
    wph
    sge0seq.g
    a1i
    feq1d
    mpbird
    #
    cZ
    cr
    cG
    frn
    syl
    cr
    cxr
    wss
    wph
    ressxr
    a1i
    sstrd
    wph
    cF
    cvv
    cZ
    cZ
    cvv
    wcel
    #
    wph
    cZ
    cM
    cuz
    cfv
    #
    cvv
    sge0seq.z
    cM
    cuz
    fvex
    eqeltri
    #
    a1i
    #
    wph
    cZ
    @15
    cc0
    cpnf
    cicc
    co
    #
    cF
    sge0seq.f
    @15
    @27
    wss
    wph
    cc0
    cpnf
    icossicc
    #
    a1i
    fssd
    sge0xrcl
    wph
    @4
    vz
    @0
    wph
    @3
    @0
    wcel
    #
    wa
    #
    vj
    cv
    #
    cG
    cfv
    #
    @3
    wceq
    #
    vj
    cZ
    wrex
    #
    @4
    @30
    @29
    @34
    wph
    @29
    simpr
    wph
    @29
    @34
    wb
    #
    @29
    wph
    cG
    cZ
    wfn
    #
    @35
    wph
    @10
    @36
    @22
    cZ
    cr
    cG
    ffn
    syl
    vj
    cZ
    @3
    cG
    fvelrnb
    syl
    adantr
    mpbid
    @30
    @33
    @4
    vj
    cZ
    wph
    @31
    cZ
    wcel
    #
    @33
    @4
    wi
    wi
    @29
    wph
    @37
    @33
    @4
    wph
    @37
    @33
    w3a
    #
    @4
    vk
    cM
    @31
    cfz
    co
    #
    @16
    cmpt
    csumge0
    cfv
    #
    vk
    cZ
    @16
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wph
    @37
    @43
    @33
    wph
    vk
    cZ
    @16
    @39
    cvv
    @26
    @14
    @15
    @27
    @16
    @28
    @17
    sseldi
    @39
    cZ
    wss
    wph
    vk
    @39
    cZ
    @12
    @39
    wcel
    #
    @12
    @24
    cZ
    @12
    cM
    @31
    elfzuz
    sge0seq.z
    syl6eleqr
    #
    ssriv
    a1i
    sge0lessmpt
    3ad2ant1
    @38
    @3
    @40
    @2
    @42
    cle
    @38
    @40
    @31
    @11
    cfv
    #
    @32
    @3
    @38
    @40
    @39
    @16
    vk
    csu
    #
    @46
    wph
    @37
    @40
    @47
    wceq
    @33
    wph
    @39
    @16
    vk
    wph
    cM
    @31
    fzfid
    #
    @44
    wph
    @13
    @16
    @15
    wcel
    #
    @45
    @17
    sylan2
    sge0fsummpt
    3ad2ant1
    wph
    @37
    @47
    @46
    wceq
    @33
    wph
    @37
    wa
    #
    @16
    vk
    cF
    cM
    @31
    @50
    @44
    wa
    #
    wph
    @13
    @16
    @16
    wceq
    wph
    @37
    @44
    simpll
    #
    @44
    @13
    @50
    @45
    adantl
    #
    @14
    @16
    eqidd
    syl2anc
    @37
    @31
    @24
    wcel
    #
    wph
    @37
    @54
    cZ
    @24
    @31
    sge0seq.z
    eleq2i
    #
    biimpi
    adantl
    #
    @51
    wph
    @13
    @16
    cc
    wcel
    @52
    @53
    @14
    @16
    @18
    recnd
    syl2anc
    fsumser
    #
    3adant3
    eqtrd
    @46
    @32
    wceq
    @38
    @31
    @11
    cG
    cG
    @11
    sge0seq.g
    eqcomi
    fveq1i
    a1i
    wph
    @37
    @33
    simp3
    3eqtrrd
    wph
    @37
    @2
    @42
    wceq
    #
    @33
    wph
    cF
    @41
    csumge0
    wph
    vk
    cZ
    @15
    cF
    sge0seq.f
    feqmptd
    #
    fveq2d
    #
    3ad2ant1
    breq12d
    mpbird
    3exp
    adantr
    rexlimdv
    mpd
    ralrimiva
    wph
    @9
    vz
    cr
    wph
    @3
    cr
    wcel
    #
    wa
    #
    @5
    @8
    @62
    @5
    wa
    #
    @3
    @47
    clt
    wbr
    #
    vj
    cZ
    wrex
    #
    @8
    @63
    @3
    vw
    cv
    #
    @16
    vk
    csu
    #
    clt
    wbr
    #
    vw
    cZ
    cpw
    #
    cfn
    cin
    #
    wrex
    @65
    @63
    vw
    cZ
    @16
    @3
    vk
    cvv
    @63
    vk
    nfv
    @23
    @63
    @25
    a1i
    wph
    @13
    @49
    @61
    @5
    @17
    ad4ant14
    wph
    @61
    @5
    simplr
    wph
    @5
    @3
    @42
    clt
    wbr
    @61
    wph
    @5
    wa
    @3
    @2
    @42
    clt
    wph
    @5
    simpr
    wph
    @58
    @5
    @60
    adantr
    breqtrd
    adantlr
    sge0gtfsumgt
    @63
    @68
    @65
    vw
    @70
    @62
    @66
    @70
    wcel
    #
    @68
    @65
    wi
    wi
    @5
    @62
    @71
    @68
    @65
    @62
    @71
    @68
    w3a
    #
    @66
    @39
    wss
    #
    vj
    cZ
    wrex
    #
    @65
    wph
    @71
    @68
    @74
    @61
    wph
    @71
    @68
    w3a
    @66
    vj
    cM
    cZ
    wph
    @71
    cM
    cz
    wcel
    @68
    sge0seq.m
    3ad2ant1
    sge0seq.z
    @71
    wph
    @66
    cZ
    wss
    @68
    @66
    cZ
    cfn
    elpwinss
    #
    3ad2ant2
    @71
    wph
    @66
    cfn
    wcel
    #
    @68
    @66
    @69
    cfn
    elinel2
    #
    3ad2ant2
    uzfissfz
    3adant1r
    @72
    @73
    @64
    vj
    cZ
    @72
    @73
    @64
    @72
    @73
    wa
    @3
    @67
    @47
    wph
    @61
    @71
    @68
    @73
    simpl1r
    @62
    @71
    @73
    @67
    cr
    wcel
    #
    @68
    wph
    @71
    @78
    @61
    @73
    wph
    @71
    wa
    #
    @66
    @16
    vk
    @71
    @76
    wph
    @77
    adantl
    @79
    @12
    @66
    wcel
    #
    wa
    cZ
    cr
    @12
    cF
    wph
    cZ
    cr
    cF
    wf
    @71
    @80
    wph
    vk
    cZ
    @16
    cr
    cF
    @59
    @18
    fmpt3d
    ad2antrr
    @71
    @80
    @13
    wph
    @71
    @66
    cZ
    @12
    @75
    sselda
    adantll
    ffvelrnd
    fsumrecl
    ad4ant13
    3adantl3
    @62
    @71
    @73
    @47
    cr
    wcel
    #
    @68
    wph
    @81
    @61
    @71
    @73
    wph
    @39
    @16
    vk
    @48
    @44
    wph
    @13
    @16
    cr
    wcel
    #
    @45
    @18
    sylan2
    #
    fsumrecl
    ad3antrrr
    3adantl3
    @62
    @71
    @68
    @73
    simpl3
    @62
    @71
    @73
    @67
    @47
    cle
    wbr
    #
    @68
    wph
    @73
    @84
    @61
    wph
    @73
    wa
    @39
    @16
    @66
    vk
    wph
    @39
    cfn
    wcel
    @73
    @48
    adantr
    wph
    @44
    @82
    @73
    @83
    adantlr
    wph
    @44
    cc0
    @16
    cle
    wbr
    #
    @73
    @44
    wph
    @13
    @85
    @45
    @14
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @49
    @85
    @86
    @14
    0xr
    a1i
    @87
    @14
    pnfxr
    a1i
    @17
    cc0
    cpnf
    @16
    icogelb
    syl3anc
    sylan2
    adantlr
    wph
    @73
    simpr
    fsumless
    adantlr
    3ad2antl1
    ltletrd
    ex
    reximdv
    mpd
    3exp
    adantr
    rexlimdv
    mpd
    @62
    @65
    @8
    wi
    @5
    @62
    @64
    @8
    vj
    cZ
    @62
    @37
    @64
    @8
    @62
    @37
    @64
    w3a
    @47
    @0
    wcel
    #
    @64
    @8
    @62
    @37
    @88
    @64
    wph
    @37
    @88
    @61
    @50
    @88
    @46
    @11
    crn
    #
    wcel
    #
    @50
    @11
    cZ
    wfn
    #
    @37
    @90
    wph
    @91
    @37
    wph
    cZ
    cr
    @11
    @20
    ffnd
    adantr
    @50
    @54
    @37
    @56
    @55
    sylibr
    cZ
    @31
    @11
    fnfvelrn
    syl2anc
    @50
    @47
    @46
    @0
    @89
    @57
    @50
    cG
    @11
    @21
    @50
    sge0seq.g
    a1i
    rneqd
    eleq12d
    mpbird
    adantlr
    3adant3
    @62
    @37
    @64
    simp3
    @7
    @64
    vy
    @47
    @0
    @6
    @47
    @3
    clt
    breq2
    rspcev
    syl2anc
    3exp
    rexlimdv
    adantr
    mpd
    ex
    ralrimiva
    vz
    vy
    @0
    @2
    supxr2
    syl22anc
    eqcomd
end
