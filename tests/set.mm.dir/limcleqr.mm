include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cmnf.mm"
include "cioo.mm"
include "cres.mm"
include "limccl.mm"
include "sseldi.mm"
include "cin.mm"
include "cpnf.mm"
include "cle.mm"
include "cif.mm"
include "simp-4r.mm"
include "simplr.mm"
include "ifcld.mm"
include "nfv.mm"
include "nfan.mm"
include "nfra1.mm"
include "w3a.mm"
include "wceq.mm"
include "simp-6l.mm"
include "3ad2antl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "rexrd.mm"
include "3ad2ant1.mm"
include "cr.mm"
include "sselda.mm"
include "3adant3.mm"
include "mnfltd.mm"
include "simp3.mm"
include "eliood.mm"
include "syl3anc.mm"
include "fvres.mm"
include "oveq1d.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "syl.mm"
include "elind.mm"
include "jca.mm"
include "simpl3l.mm"
include "adantr.mm"
include "simpl3r.mm"
include "simpl1.mm"
include "simprr.mm"
include "recnd.mm"
include "subcld.mm"
include "abscld.mm"
include "syl2anc.mm"
include "rpre.mm"
include "adantl.mm"
include "3adant1.mm"
include "simprl.mm"
include "min1.mm"
include "ltletrd.mm"
include "syl32anc.mm"
include "rspa.mm"
include "sylc.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "id.mm"
include "necomd.mm"
include "ad2antrr.mm"
include "3ad2antl3.mm"
include "lttri5d.mm"
include "pnfxr.mm"
include "ltpnfd.mm"
include "simpl1r.mm"
include "min2.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "3exp.mm"
include "ralrimi.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "wf.mm"
include "fresin.mm"
include "wss.mm"
include "inss2.mm"
include "ioosscn.mm"
include "sstri.mm"
include "ellimc3.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "wb.mm"
include "oveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "mpbird.mm"
include "r19.29a.mm"
include "ioossre.mm"
include "ax-resscn.mm"
include "syl5ss.mm"
include "ralrimiva.mm"
include "syl6ss.mm"
include "mpbir2and.mm"

theorem limcleqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume limcleqr.k: |- K = ( TopOpen ` CCfld )
  assume limcleqr.a: |- ( ph -> A C_ RR )
  assume limcleqr.j: |- J = ( topGen ` ran (,) )
  assume limcleqr.f: |- ( ph -> F : A --> CC )
  assume limcleqr.b: |- ( ph -> B e. RR )
  assume limcleqr.l: |- ( ph -> L e. ( ( F |` ( -oo (,) B ) ) limCC B ) )
  assume limcleqr.r: |- ( ph -> R e. ( ( F |` ( B (,) +oo ) ) limCC B ) )
  assume limcleqr.leqr: |- ( ph -> L = R )


  assert |- ( ph -> L e. ( F limCC B ) )

  proof
    wph
    cL
    cF
    cB
    climc
    co
    wcel
    cL
    cc
    wcel
    #
    vz
    cv
    #
    cB
    wne
    #
    @1
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wa
    #
    @1
    cF
    cfv
    #
    cL
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cA
    wral
    #
    vy
    crp
    wrex
    #
    vx
    crp
    wral
    wph
    cF
    cmnf
    cB
    cioo
    co
    #
    cres
    #
    cB
    climc
    co
    #
    cc
    cL
    cB
    @17
    limccl
    limcleqr.l
    sseldi
    wph
    @15
    vx
    crp
    wph
    @11
    crp
    wcel
    #
    wa
    #
    @2
    @4
    va
    cv
    #
    clt
    wbr
    #
    wa
    #
    @1
    @17
    cfv
    #
    cL
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    #
    vz
    cA
    @16
    cin
    #
    wral
    #
    @15
    va
    crp
    @20
    @21
    crp
    wcel
    #
    wa
    #
    @30
    wa
    #
    @2
    @4
    vb
    cv
    #
    clt
    wbr
    #
    wa
    #
    @1
    cF
    cB
    cpnf
    cioo
    co
    #
    cres
    #
    cfv
    #
    cL
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    #
    vz
    cA
    @37
    cin
    #
    wral
    #
    @15
    vb
    crp
    @33
    @34
    crp
    wcel
    #
    wa
    #
    @45
    wa
    #
    @21
    @34
    cle
    wbr
    #
    @21
    @34
    cif
    #
    crp
    wcel
    @2
    @4
    @50
    clt
    wbr
    #
    wa
    #
    @12
    wi
    #
    vz
    cA
    wral
    #
    @15
    @48
    @49
    @21
    @34
    crp
    @20
    @31
    @30
    @46
    @45
    simp-4r
    #
    @33
    @46
    @45
    simplr
    #
    ifcld
    @48
    @53
    vz
    cA
    @47
    @45
    vz
    @33
    @46
    vz
    @32
    @30
    vz
    @20
    @31
    vz
    @20
    vz
    nfv
    @31
    vz
    nfv
    nfan
    @28
    vz
    @29
    nfra1
    nfan
    @46
    vz
    nfv
    nfan
    @43
    vz
    @44
    nfra1
    nfan
    @48
    @1
    cA
    wcel
    #
    @52
    @12
    @48
    @57
    @52
    w3a
    #
    @1
    cB
    clt
    wbr
    #
    @12
    @58
    @59
    wa
    #
    @10
    @26
    @11
    clt
    @60
    @1
    @16
    wcel
    #
    @10
    @26
    wceq
    @60
    wph
    @57
    @59
    @61
    @48
    @57
    @59
    wph
    @52
    wph
    @19
    @31
    @30
    @46
    @45
    @59
    simp-6l
    3ad2antl1
    #
    @48
    @57
    @52
    @59
    simpl2
    #
    @58
    @59
    simpr
    wph
    @57
    @59
    w3a
    #
    cmnf
    cB
    @1
    cmnf
    cxr
    wcel
    @64
    mnfxr
    a1i
    wph
    @57
    cB
    cxr
    wcel
    #
    @59
    wph
    cB
    limcleqr.b
    rexrd
    #
    3ad2ant1
    wph
    @57
    @1
    cr
    wcel
    #
    @59
    wph
    cA
    cr
    @1
    limcleqr.a
    sselda
    #
    3adant3
    #
    @64
    @1
    @69
    mnfltd
    wph
    @57
    @59
    simp3
    eliood
    syl3anc
    #
    @61
    @9
    @25
    cabs
    @61
    @25
    @9
    @61
    @24
    @8
    cL
    cmin
    @1
    @16
    cF
    fvres
    oveq1d
    eqcomd
    fveq2d
    syl
    @60
    @30
    @1
    @29
    wcel
    #
    wa
    @23
    @27
    @60
    @30
    @71
    @48
    @57
    @59
    @30
    @52
    @32
    @30
    @46
    @45
    @59
    simp-4r
    3ad2antl1
    @60
    cA
    @16
    @1
    @63
    @70
    elind
    jca
    @60
    @2
    @22
    @2
    @51
    @48
    @57
    @59
    simpl3l
    @60
    wph
    @31
    @46
    @51
    @57
    @22
    @62
    @48
    @57
    @59
    @31
    @52
    @48
    @31
    @59
    @55
    adantr
    3ad2antl1
    @48
    @57
    @59
    @46
    @52
    @48
    @46
    @59
    @56
    adantr
    3ad2antl1
    @2
    @51
    @48
    @57
    @59
    simpl3r
    @63
    wph
    @31
    @46
    w3a
    #
    @51
    @57
    wa
    #
    wa
    #
    @4
    @50
    @21
    @74
    wph
    @57
    @4
    cr
    wcel
    wph
    @31
    @46
    @73
    simpl1
    @72
    @51
    @57
    simprr
    wph
    @57
    wa
    #
    @3
    @75
    @1
    cB
    @75
    @1
    @68
    recnd
    wph
    cB
    cc
    wcel
    @57
    wph
    cB
    limcleqr.b
    recnd
    #
    adantr
    subcld
    abscld
    syl2anc
    #
    @72
    @50
    cr
    wcel
    #
    @73
    @31
    @46
    @78
    wph
    @31
    @46
    wa
    @49
    @21
    @34
    cr
    @31
    @21
    cr
    wcel
    #
    @46
    @21
    rpre
    adantr
    #
    @46
    @34
    cr
    wcel
    #
    @31
    @34
    rpre
    adantl
    #
    ifcld
    3adant1
    adantr
    #
    @72
    @79
    @73
    @31
    @46
    @79
    wph
    @80
    3adant1
    #
    adantr
    @72
    @51
    @57
    simprl
    #
    @72
    @50
    @21
    cle
    wbr
    #
    @73
    @72
    @79
    @81
    @86
    @84
    @31
    @46
    @81
    wph
    @82
    3adant1
    #
    @21
    @34
    min1
    syl2anc
    adantr
    ltletrd
    syl32anc
    jca
    @28
    vz
    @29
    rspa
    sylc
    eqbrtrd
    @58
    @59
    wn
    #
    cB
    @1
    clt
    wbr
    #
    @12
    @58
    @88
    wa
    #
    cB
    @1
    @90
    wph
    cB
    cr
    wcel
    @48
    @57
    @88
    wph
    @52
    wph
    @19
    @31
    @30
    @46
    @45
    @88
    simp-6l
    3ad2antl1
    #
    limcleqr.b
    syl
    @90
    wph
    @57
    @67
    @91
    @48
    @57
    @52
    @88
    simpl2
    @68
    syl2anc
    @52
    @48
    @88
    cB
    @1
    wne
    #
    @57
    @2
    @92
    @51
    @88
    @2
    @1
    cB
    @2
    id
    necomd
    ad2antrr
    3ad2antl3
    @58
    @88
    simpr
    lttri5d
    @58
    @89
    wa
    #
    @10
    @41
    @11
    clt
    @93
    @1
    @37
    wcel
    #
    @10
    @41
    wceq
    @93
    wph
    @57
    @89
    @94
    @48
    @57
    @89
    wph
    @52
    wph
    @19
    @31
    @30
    @46
    @45
    @89
    simp-6l
    3ad2antl1
    #
    @48
    @57
    @52
    @89
    simpl2
    #
    @58
    @89
    simpr
    wph
    @57
    @89
    w3a
    #
    cB
    cpnf
    @1
    wph
    @57
    @65
    @89
    @66
    3ad2ant1
    cpnf
    cxr
    wcel
    @97
    pnfxr
    a1i
    wph
    @57
    @67
    @89
    @68
    3adant3
    #
    wph
    @57
    @89
    simp3
    @97
    @1
    @98
    ltpnfd
    eliood
    syl3anc
    #
    @94
    @9
    @40
    cabs
    @94
    @8
    @39
    cL
    cmin
    @94
    @39
    @8
    @1
    @37
    cF
    fvres
    eqcomd
    oveq1d
    fveq2d
    syl
    @93
    @45
    @1
    @44
    wcel
    #
    wa
    @36
    @42
    @93
    @45
    @100
    @47
    @45
    @57
    @52
    @89
    simpl1r
    @93
    cA
    @37
    @1
    @96
    @99
    elind
    jca
    @93
    @2
    @35
    @2
    @51
    @48
    @57
    @89
    simpl3l
    @93
    wph
    @31
    @46
    @51
    @57
    @35
    @95
    @48
    @57
    @89
    @31
    @52
    @48
    @31
    @89
    @55
    adantr
    3ad2antl1
    @48
    @57
    @89
    @46
    @52
    @48
    @46
    @89
    @56
    adantr
    3ad2antl1
    @2
    @51
    @48
    @57
    @89
    simpl3r
    @96
    @74
    @4
    @50
    @34
    @77
    @83
    @72
    @81
    @73
    @87
    adantr
    @85
    @72
    @50
    @34
    cle
    wbr
    #
    @73
    @72
    @79
    @81
    @101
    @84
    @87
    @21
    @34
    min2
    syl2anc
    adantr
    ltletrd
    syl32anc
    jca
    @43
    vz
    @44
    rspa
    sylc
    eqbrtrd
    syldan
    pm2.61dan
    3exp
    ralrimi
    @14
    @54
    vy
    @50
    crp
    @5
    @50
    wceq
    #
    @13
    @53
    vz
    cA
    @102
    @7
    @52
    @12
    @102
    @6
    @51
    @2
    @5
    @50
    @4
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    @20
    @45
    vb
    crp
    wrex
    #
    @31
    @30
    @20
    @103
    @36
    @39
    cR
    cmin
    co
    #
    cabs
    cfv
    #
    @11
    clt
    wbr
    #
    wi
    #
    vz
    @44
    wral
    vb
    crp
    wrex
    #
    wph
    @108
    vx
    crp
    wph
    cR
    cc
    wcel
    #
    @108
    vx
    crp
    wral
    #
    wph
    cR
    @38
    cB
    climc
    co
    wcel
    @109
    @110
    wa
    limcleqr.r
    wph
    vx
    vb
    vz
    @44
    cB
    cR
    @38
    wph
    cA
    cc
    cF
    wf
    #
    @44
    cc
    @38
    wf
    limcleqr.f
    cA
    cc
    cF
    @37
    fresin
    syl
    @44
    cc
    wss
    wph
    @44
    @37
    cc
    cA
    @37
    inss2
    cB
    cpnf
    ioosscn
    sstri
    a1i
    @76
    ellimc3
    mpbid
    simprd
    r19.21bi
    wph
    @103
    @108
    wb
    @19
    wph
    @43
    @107
    vb
    vz
    crp
    @44
    wph
    @42
    @106
    @36
    wph
    @41
    @105
    @11
    clt
    wph
    @40
    @104
    cabs
    wph
    cL
    cR
    @39
    cmin
    limcleqr.leqr
    oveq2d
    fveq2d
    breq1d
    imbi2d
    rexralbidv
    adantr
    mpbird
    ad2antrr
    r19.29a
    wph
    @30
    va
    crp
    wrex
    #
    vx
    crp
    wph
    @0
    @112
    vx
    crp
    wral
    #
    wph
    cL
    @18
    wcel
    @0
    @113
    wa
    limcleqr.l
    wph
    vx
    va
    vz
    @29
    cB
    cL
    @17
    wph
    @111
    @29
    cc
    @17
    wf
    limcleqr.f
    cA
    cc
    cF
    @16
    fresin
    syl
    wph
    @29
    cr
    cc
    @29
    @16
    cr
    cA
    @16
    inss2
    cmnf
    cB
    ioossre
    sstri
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    syl5ss
    @76
    ellimc3
    mpbid
    simprd
    r19.21bi
    r19.29a
    ralrimiva
    wph
    vx
    vy
    vz
    cA
    cB
    cL
    cF
    limcleqr.f
    wph
    cA
    cr
    cc
    limcleqr.a
    ax-resscn
    syl6ss
    @76
    ellimc3
    mpbir2and
end
