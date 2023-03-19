include "cfv.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cn0.mm"
include "cidom.mm"
include "crg.mm"
include "wne.mm"
include "ccrg.mm"
include "cdomn.mm"
include "isidom.mm"
include "simplbi.mm"
include "crngring.mm"
include "3syl.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "eqeq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "wa.mm"
include "c0.mm"
include "wn.mm"
include "simprr.mm"
include "0nn0.mm"
include "syl6eqel.mm"
include "wb.mm"
include "syl.mm"
include "simpl.mm"
include "deg1nn0clb.mm"
include "syl2an.mm"
include "mpbird.mm"
include "cco1.mm"
include "cascl.mm"
include "simplrr.mm"
include "0le0.mm"
include "syl6eqbr.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "deg1le0.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cbs.mm"
include "cxp.mm"
include "fveq2d.mm"
include "adantr.mm"
include "wf.mm"
include "coe1f.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "evl1sca.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "wfn.mm"
include "cpws.mm"
include "cvv.mm"
include "fvexd.mm"
include "crh.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "pwselbas.mm"
include "ffn.mm"
include "fniniseg.mm"
include "simplbda.mm"
include "simprbda.mm"
include "fvex.mm"
include "fvconst2.mm"
include "3eqtr3rd.mm"
include "ply1scl0.mm"
include "3eqtrd.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"
include "eq0rdv.mm"
include "hash0.mm"
include "syl6eq.mm"
include "syl5breqr.mm"
include "eqbrtrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "peano2nn0.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "nn0ge0d.mm"
include "breq1d.mm"
include "syl5ibrcom.mm"
include "a1dd.mm"
include "wex.mm"
include "n0.mm"
include "cv1.mm"
include "csg.mm"
include "simplll.mm"
include "simpllr.mm"
include "fta1glem2.mm"
include "exp32.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "com23.mm"
include "ralrimdva.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "sylc.mm"
include "rspcv.mm"
include "mpi.mm"

theorem fta1g
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cN: class N
  let cG: class G
  let cT: class T
  assume fta1g.p: |- P = ( Poly1 ` R )
  assume fta1g.b: |- B = ( Base ` P )
  assume fta1g.d: |- D = ( deg1 ` R )
  assume fta1g.o: |- O = ( eval1 ` R )
  assume fta1g.w: |- W = ( 0g ` R )
  assume fta1g.z: |- .0. = ( 0g ` P )
  assume fta1g.1: |- ( ph -> R e. IDomn )
  assume fta1g.2: |- ( ph -> F e. B )
  assume fta1g.3: |- ( ph -> F =/= .0. )


  assert |- ( ph -> ( # ` ( `' ( O ` F ) " { W } ) ) <_ ( D ` F ) )

  proof
    wph
    cF
    cD
    cfv
    #
    @0
    wceq
    #
    cF
    cO
    cfv
    #
    ccnv
    #
    cW
    csn
    #
    cima
    #
    chash
    cfv
    #
    @0
    cle
    wbr
    #
    @0
    eqid
    wph
    cF
    cB
    wcel
    #
    vf
    cv
    #
    cD
    cfv
    #
    @0
    wceq
    #
    @9
    cO
    cfv
    #
    ccnv
    #
    @4
    cima
    #
    chash
    cfv
    #
    @10
    cle
    wbr
    #
    wi
    #
    vf
    cB
    wral
    #
    @1
    @7
    wi
    #
    fta1g.2
    wph
    @0
    cn0
    wcel
    #
    cR
    cidom
    wcel
    #
    @18
    wph
    cR
    crg
    wcel
    #
    @8
    cF
    c.0
    wne
    @20
    wph
    @21
    cR
    ccrg
    wcel
    #
    @22
    fta1g.1
    @21
    @23
    cR
    cdomn
    wcel
    cR
    isidom
    simplbi
    #
    cR
    crngring
    #
    3syl
    fta1g.2
    fta1g.3
    cB
    cD
    cP
    cR
    cF
    c.0
    fta1g.d
    fta1g.p
    fta1g.z
    fta1g.b
    deg1nn0cl
    syl3anc
    fta1g.1
    @21
    @10
    vx
    cv
    #
    wceq
    #
    @16
    wi
    #
    vf
    cB
    wral
    #
    wi
    @21
    @10
    cc0
    wceq
    #
    @16
    wi
    #
    vf
    cB
    wral
    #
    wi
    @21
    @10
    vd
    cv
    #
    wceq
    #
    @16
    wi
    #
    vf
    cB
    wral
    #
    wi
    @21
    @10
    @33
    c1
    caddc
    co
    #
    wceq
    #
    @16
    wi
    #
    vf
    cB
    wral
    #
    wi
    @21
    @18
    wi
    vx
    vd
    @0
    @26
    cc0
    wceq
    #
    @29
    @32
    @21
    @41
    @28
    @31
    vf
    cB
    @41
    @27
    @30
    @16
    @26
    cc0
    @10
    eqeq2
    imbi1d
    ralbidv
    imbi2d
    @26
    @33
    wceq
    #
    @29
    @36
    @21
    @42
    @28
    @35
    vf
    cB
    @42
    @27
    @34
    @16
    @26
    @33
    @10
    eqeq2
    imbi1d
    ralbidv
    imbi2d
    @26
    @37
    wceq
    #
    @29
    @40
    @21
    @43
    @28
    @39
    vf
    cB
    @43
    @27
    @38
    @16
    @26
    @37
    @10
    eqeq2
    imbi1d
    ralbidv
    imbi2d
    @26
    @0
    wceq
    #
    @29
    @18
    @21
    @44
    @28
    @17
    vf
    cB
    @44
    @27
    @11
    @16
    @26
    @0
    @10
    eqeq2
    imbi1d
    ralbidv
    imbi2d
    @21
    @31
    vf
    cB
    @21
    @9
    cB
    wcel
    #
    @30
    @16
    @21
    @45
    @30
    wa
    #
    wa
    #
    @15
    cc0
    @10
    cle
    @47
    @15
    c0
    chash
    cfv
    #
    cc0
    @47
    @14
    c0
    chash
    @47
    vx
    @14
    @47
    @9
    c.0
    wne
    #
    @26
    @14
    wcel
    #
    wn
    @47
    @49
    @10
    cn0
    wcel
    #
    @47
    @10
    cc0
    cn0
    @21
    @45
    @30
    simprr
    #
    0nn0
    syl6eqel
    @21
    @22
    @45
    @49
    @51
    wb
    @46
    @21
    @23
    @22
    @24
    @25
    syl
    #
    @45
    @30
    simpl
    cB
    cD
    cP
    cR
    @9
    c.0
    fta1g.d
    fta1g.p
    fta1g.z
    fta1g.b
    deg1nn0clb
    syl2an
    mpbird
    @47
    @50
    @9
    c.0
    @47
    @50
    @9
    c.0
    wceq
    @47
    @50
    wa
    #
    @9
    cc0
    @9
    cco1
    cfv
    #
    cfv
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cW
    @57
    cfv
    #
    c.0
    @54
    @10
    cc0
    cle
    wbr
    #
    @9
    @58
    wceq
    #
    @54
    @10
    cc0
    cc0
    cle
    @21
    @45
    @30
    @50
    simplrr
    0le0
    syl6eqbr
    @54
    @22
    @45
    @60
    @61
    wb
    @21
    @22
    @46
    @50
    @53
    ad2antrr
    #
    @21
    @45
    @30
    @50
    simplrl
    #
    @57
    cB
    cD
    cP
    cR
    @9
    fta1g.d
    fta1g.p
    fta1g.b
    @57
    eqid
    #
    deg1le0
    syl2anc
    mpbid
    #
    @54
    @56
    cW
    @57
    @54
    @26
    @12
    cfv
    #
    @26
    cR
    cbs
    cfv
    #
    @56
    csn
    cxp
    #
    cfv
    #
    cW
    @56
    @54
    @26
    @12
    @68
    @54
    @12
    @58
    cO
    cfv
    #
    @68
    @54
    @9
    @58
    cO
    @65
    fveq2d
    @54
    @23
    @56
    @67
    wcel
    #
    @70
    @68
    wceq
    @47
    @23
    @50
    @21
    @23
    @46
    @24
    adantr
    #
    adantr
    @54
    cn0
    @67
    @55
    wf
    #
    cc0
    cn0
    wcel
    @71
    @54
    @45
    @73
    @63
    @55
    cB
    cP
    cR
    @9
    @67
    @55
    eqid
    fta1g.b
    fta1g.p
    @67
    eqid
    #
    coe1f
    syl
    0nn0
    cn0
    @67
    cc0
    @55
    ffvelrn
    sylancl
    @57
    @67
    cP
    cR
    cO
    @56
    fta1g.o
    fta1g.p
    @74
    @64
    evl1sca
    syl2anc
    eqtrd
    fveq1d
    @47
    @50
    @26
    @67
    wcel
    #
    @66
    cW
    wceq
    #
    @47
    @67
    @67
    @12
    wf
    @12
    @67
    wfn
    @50
    @75
    @76
    wa
    wb
    @47
    @67
    cR
    @67
    cR
    @67
    cpws
    co
    #
    cbs
    cfv
    #
    cidom
    @12
    @77
    cvv
    @77
    eqid
    #
    @74
    @78
    eqid
    #
    @21
    @46
    simpl
    @47
    cR
    cbs
    fvexd
    @47
    cB
    @78
    @9
    cO
    @47
    @23
    cO
    cP
    @77
    crh
    co
    wcel
    cB
    @78
    cO
    wf
    @72
    @67
    cP
    cR
    @77
    cO
    fta1g.o
    fta1g.p
    @79
    @74
    evl1rhm
    cB
    @78
    cP
    @77
    cO
    fta1g.b
    @80
    rhmf
    3syl
    @21
    @45
    @30
    simprl
    ffvelrnd
    pwselbas
    @67
    @67
    @12
    ffn
    @67
    cW
    @26
    @12
    fniniseg
    3syl
    #
    simplbda
    @54
    @75
    @69
    @56
    wceq
    @47
    @50
    @75
    @76
    @81
    simprbda
    @67
    @56
    @26
    cc0
    @55
    fvex
    fvconst2
    syl
    3eqtr3rd
    fveq2d
    @54
    @22
    @59
    c.0
    wceq
    @62
    @57
    cP
    cR
    c.0
    cW
    fta1g.p
    @64
    fta1g.w
    fta1g.z
    ply1scl0
    syl
    3eqtrd
    ex
    necon3ad
    mpd
    eq0rdv
    fveq2d
    hash0
    syl6eq
    @47
    cc0
    cc0
    @10
    cle
    0le0
    @52
    syl5breqr
    eqbrtrd
    expr
    ralrimiva
    @33
    cn0
    wcel
    #
    @21
    @36
    @40
    @21
    @82
    @36
    @40
    wi
    @36
    vg
    cv
    #
    cD
    cfv
    #
    @33
    wceq
    #
    @83
    cO
    cfv
    #
    ccnv
    #
    @4
    cima
    #
    chash
    cfv
    #
    @84
    cle
    wbr
    #
    wi
    #
    vg
    cB
    wral
    #
    @21
    @82
    wa
    #
    @40
    @35
    @91
    vf
    vg
    cB
    @9
    @83
    wceq
    #
    @34
    @85
    @16
    @90
    @94
    @10
    @84
    @33
    @9
    @83
    cD
    fveq2
    #
    eqeq1d
    @94
    @15
    @89
    @10
    @84
    cle
    @94
    @14
    @88
    chash
    @94
    @13
    @87
    @4
    @94
    @12
    @86
    @9
    @83
    cO
    fveq2
    cnveqd
    imaeq1d
    fveq2d
    @95
    breq12d
    imbi12d
    cbvralv
    @93
    @92
    @39
    vf
    cB
    @93
    @45
    wa
    @38
    @92
    @16
    @93
    @45
    @38
    @92
    @16
    wi
    #
    @93
    @45
    @38
    wa
    #
    wa
    #
    @96
    @14
    c0
    @98
    @14
    c0
    wceq
    #
    @16
    @92
    @98
    @16
    @99
    cc0
    @10
    cle
    wbr
    @98
    @10
    @98
    @10
    @37
    cn0
    @93
    @45
    @38
    simprr
    @82
    @37
    cn0
    wcel
    @21
    @97
    @33
    peano2nn0
    ad2antlr
    eqeltrd
    nn0ge0d
    @99
    @15
    cc0
    @10
    cle
    @99
    @15
    @48
    cc0
    @14
    c0
    chash
    fveq2
    hash0
    syl6eq
    breq1d
    syl5ibrcom
    a1dd
    @14
    c0
    wne
    @50
    vx
    wex
    @98
    @96
    vx
    @14
    n0
    @98
    @50
    @96
    vx
    @98
    @50
    @92
    @16
    @98
    @50
    @92
    wa
    #
    wa
    @57
    cB
    cD
    cP
    cR
    @26
    vg
    @9
    cR
    cv1
    cfv
    #
    @26
    @57
    cfv
    cP
    csg
    cfv
    #
    co
    #
    @67
    @102
    @33
    cO
    cW
    @101
    c.0
    fta1g.p
    fta1g.b
    fta1g.d
    fta1g.o
    fta1g.w
    fta1g.z
    @21
    @82
    @97
    @100
    simplll
    @93
    @45
    @38
    @100
    simplrl
    @74
    @101
    eqid
    @102
    eqid
    @64
    @103
    eqid
    @21
    @82
    @97
    @100
    simpllr
    @93
    @45
    @38
    @100
    simplrr
    @98
    @50
    @92
    simprl
    @98
    @50
    @92
    simprr
    fta1glem2
    exp32
    exlimdv
    syl5bi
    pm2.61dne
    expr
    com23
    ralrimdva
    syl5bi
    expcom
    a2d
    nn0ind
    sylc
    @17
    @19
    vf
    cF
    cB
    @9
    cF
    wceq
    #
    @11
    @1
    @16
    @7
    @104
    @10
    @0
    @0
    @9
    cF
    cD
    fveq2
    #
    eqeq1d
    @104
    @15
    @6
    @10
    @0
    cle
    @104
    @14
    @5
    chash
    @104
    @13
    @3
    @4
    @104
    @12
    @2
    @9
    cF
    cO
    fveq2
    cnveqd
    imaeq1d
    fveq2d
    @105
    breq12d
    imbi12d
    rspcv
    sylc
    mpi
end
