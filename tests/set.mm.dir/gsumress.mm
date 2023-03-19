include "crn.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "c0g.mm"
include "cfv.mm"
include "cfz.mm"
include "wcel.mm"
include "cseq.mm"
include "cuz.mm"
include "wrex.mm"
include "wex.mm"
include "cio.mm"
include "c1.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "chash.mm"
include "wf1o.mm"
include "ccom.mm"
include "cif.mm"
include "cplusg.mm"
include "cbs.mm"
include "cgsu.mm"
include "sseldd.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "eqid.mm"
include "mgmidsssn0.mm"
include "syl.mm"
include "elsni.mm"
include "sneqd.mm"
include "sseqtr4d.mm"
include "eqssd.mm"
include "sselda.mm"
include "syldan.mm"
include "ressbas2.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "ressplusg.mm"
include "oveqd.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "eleqtrd.mm"
include "cress.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "eqtr3d.mm"
include "sseq2d.mm"
include "seqeq2d.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "exbidv.mm"
include "iotabidv.mm"
include "ifeq12d.mm"
include "ifbieq12d.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "fssd.mm"
include "gsumval.mm"
include "wf.mm"
include "feq3d.mm"
include "mpbid.mm"
include "3eqtr4d.mm"

theorem gsumress
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z
  assume gsumress.b: |- B = ( Base ` G )
  assume gsumress.o: |- .+ = ( +g ` G )
  assume gsumress.h: |- H = ( G |`s S )
  assume gsumress.g: |- ( ph -> G e. V )
  assume gsumress.a: |- ( ph -> A e. X )
  assume gsumress.s: |- ( ph -> S C_ B )
  assume gsumress.f: |- ( ph -> F : A --> S )
  assume gsumress.z: |- ( ph -> .0. e. S )
  assume gsumress.c: |- ( ( ph /\ x e. B ) -> ( ( .0. .+ x ) = x /\ ( x .+ .0. ) = x ) )

  disjoint B x
  disjoint G x
  disjoint ph x
  disjoint S x
  disjoint H x
  disjoint .+ x
  disjoint .0. x
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G y
  disjoint G z
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint F f
  disjoint F m
  disjoint F n
  disjoint F z
  disjoint H f
  disjoint H m
  disjoint H n
  disjoint H y
  disjoint H z
  disjoint .+ f
  disjoint .+ m
  disjoint .+ n
  disjoint .+ y
  disjoint .+ z
  disjoint .0. y
  disjoint V y
  assert |- ( ph -> ( G gsum F ) = ( H gsum F ) )

  proof
    wph
    cF
    crn
    #
    vy
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    @2
    wceq
    #
    @2
    @1
    c.pl
    co
    #
    @2
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    vy
    cB
    crab
    #
    wss
    #
    cG
    c0g
    cfv
    #
    cA
    cfz
    crn
    wcel
    #
    cA
    vm
    cv
    #
    vn
    cv
    #
    cfz
    co
    wceq
    #
    vz
    cv
    #
    @14
    c.pl
    cF
    @13
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @13
    cuz
    cfv
    #
    wrex
    #
    vm
    wex
    #
    vz
    cio
    #
    c1
    cF
    ccnv
    #
    cvv
    c.0
    csn
    #
    cdif
    #
    cima
    #
    chash
    cfv
    #
    cfz
    co
    @28
    vf
    cv
    #
    wf1o
    #
    @16
    @29
    c.pl
    cF
    @30
    ccom
    #
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vz
    cio
    #
    cif
    #
    cif
    @0
    @1
    @2
    cH
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    @2
    @1
    @40
    co
    #
    @2
    wceq
    #
    wa
    #
    vx
    cH
    cbs
    cfv
    #
    wral
    #
    vy
    @46
    crab
    #
    wss
    #
    cH
    c0g
    cfv
    #
    @12
    @15
    @16
    @14
    @40
    cF
    @13
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vn
    @21
    wrex
    #
    vm
    wex
    #
    vz
    cio
    #
    @31
    @16
    @29
    @40
    @32
    c1
    cseq
    #
    cfv
    #
    wceq
    #
    wa
    #
    vf
    wex
    #
    vz
    cio
    #
    cif
    #
    cif
    cG
    cF
    cgsu
    co
    cH
    cF
    cgsu
    co
    wph
    @10
    @49
    @11
    @39
    @50
    @64
    wph
    @9
    @48
    @0
    wph
    @26
    @9
    @48
    wph
    @26
    @9
    wph
    c.0
    @9
    wph
    c.0
    cB
    wcel
    c.0
    @2
    c.pl
    co
    #
    @2
    wceq
    #
    @2
    c.0
    c.pl
    co
    #
    @2
    wceq
    #
    wa
    #
    vx
    cB
    wral
    #
    c.0
    @9
    wcel
    wph
    cS
    cB
    c.0
    gsumress.s
    gsumress.z
    sseldd
    wph
    @69
    vx
    cB
    gsumress.c
    ralrimiva
    @8
    @70
    vy
    c.0
    cB
    @1
    c.0
    wceq
    #
    @7
    @69
    vx
    cB
    @71
    @4
    @66
    @6
    @68
    @71
    @3
    @65
    @2
    @1
    c.0
    @2
    c.pl
    oveq1
    eqeq1d
    @71
    @5
    @67
    @2
    @1
    c.0
    @2
    c.pl
    oveq2
    eqeq1d
    anbi12d
    #
    ralbidv
    elrab
    sylanbrc
    #
    snssd
    wph
    @9
    @11
    csn
    #
    @26
    wph
    cG
    cV
    wcel
    @9
    @74
    wss
    gsumress.g
    vy
    vx
    cB
    c.pl
    cG
    @9
    cV
    @11
    gsumress.b
    @11
    eqid
    #
    gsumress.o
    @9
    eqid
    #
    mgmidsssn0
    syl
    #
    wph
    c.0
    @11
    wph
    c.0
    @74
    wcel
    c.0
    @11
    wceq
    wph
    @9
    @74
    c.0
    @77
    @73
    sseldd
    c.0
    @11
    elsni
    syl
    #
    sneqd
    sseqtr4d
    eqssd
    #
    wph
    @26
    @48
    wph
    c.0
    @48
    wph
    c.0
    @7
    vx
    cS
    wral
    #
    vy
    cS
    crab
    #
    @48
    wph
    c.0
    cS
    wcel
    @69
    vx
    cS
    wral
    #
    c.0
    @81
    wcel
    gsumress.z
    wph
    @69
    vx
    cS
    wph
    @2
    cS
    wcel
    @2
    cB
    wcel
    @69
    wph
    cS
    cB
    @2
    gsumress.s
    sselda
    gsumress.c
    syldan
    ralrimiva
    @80
    @82
    vy
    c.0
    cS
    @71
    @7
    @69
    vx
    cS
    @72
    ralbidv
    elrab
    sylanbrc
    wph
    @80
    @47
    vy
    cS
    @46
    wph
    cS
    cB
    wss
    cS
    @46
    wceq
    gsumress.s
    cS
    cB
    cH
    cG
    gsumress.h
    gsumress.b
    ressbas2
    syl
    #
    wph
    @7
    @45
    vx
    cS
    @46
    @83
    wph
    @4
    @42
    @6
    @44
    wph
    @3
    @41
    @2
    wph
    c.pl
    @40
    @1
    @2
    wph
    cS
    cvv
    wcel
    c.pl
    @40
    wceq
    wph
    cS
    @46
    cvv
    @83
    cH
    cbs
    fvex
    syl6eqel
    cS
    c.pl
    cG
    cH
    cvv
    gsumress.h
    gsumress.o
    ressplusg
    syl
    #
    oveqd
    eqeq1d
    wph
    @5
    @43
    @2
    wph
    c.pl
    @40
    @2
    @1
    @84
    oveqd
    eqeq1d
    anbi12d
    raleqbidv
    rabeqbidv
    eleqtrd
    #
    snssd
    wph
    @48
    @50
    csn
    #
    @26
    wph
    cH
    cvv
    wcel
    #
    @48
    @86
    wss
    @87
    wph
    cH
    cG
    cS
    cress
    co
    cvv
    gsumress.h
    cG
    cS
    cress
    ovex
    eqeltri
    a1i
    #
    vy
    vx
    @46
    @40
    cH
    @48
    cvv
    @50
    @46
    eqid
    #
    @50
    eqid
    #
    @40
    eqid
    #
    @48
    eqid
    #
    mgmidsssn0
    syl
    #
    wph
    c.0
    @50
    wph
    c.0
    @86
    wcel
    c.0
    @50
    wceq
    wph
    @48
    @86
    c.0
    @93
    @85
    sseldd
    c.0
    @50
    elsni
    syl
    #
    sneqd
    sseqtr4d
    eqssd
    #
    eqtr3d
    sseq2d
    wph
    c.0
    @11
    @50
    @78
    @94
    eqtr3d
    wph
    @12
    @24
    @57
    @38
    @63
    wph
    @23
    @56
    vz
    wph
    @22
    @55
    vm
    wph
    @20
    @54
    vn
    @21
    wph
    @19
    @53
    @15
    wph
    @18
    @52
    @16
    wph
    @14
    @17
    @51
    wph
    c.pl
    @40
    cF
    @13
    @84
    seqeq2d
    fveq1d
    eqeq2d
    anbi2d
    rexbidv
    exbidv
    iotabidv
    wph
    @37
    @62
    vz
    wph
    @36
    @61
    vf
    wph
    @35
    @60
    @31
    wph
    @34
    @59
    @16
    wph
    @29
    @33
    @58
    wph
    c.pl
    @40
    @32
    c1
    @84
    seqeq2d
    fveq1d
    eqeq2d
    anbi2d
    exbidv
    iotabidv
    ifeq12d
    ifbieq12d
    wph
    vz
    vx
    cA
    cB
    c.pl
    vf
    vm
    vn
    cF
    cG
    @9
    cV
    @28
    cX
    @11
    vy
    gsumress.b
    @75
    gsumress.o
    @76
    wph
    @27
    cvv
    @9
    cdif
    @25
    wph
    @26
    @9
    cvv
    @79
    difeq2d
    imaeq2d
    gsumress.g
    gsumress.a
    wph
    cA
    cS
    cB
    cF
    gsumress.f
    gsumress.s
    fssd
    gsumval
    wph
    vz
    vx
    cA
    @46
    @40
    vf
    vm
    vn
    cF
    cH
    @48
    cvv
    @28
    cX
    @50
    vy
    @89
    @90
    @91
    @92
    wph
    @27
    cvv
    @48
    cdif
    @25
    wph
    @26
    @48
    cvv
    @95
    difeq2d
    imaeq2d
    @88
    gsumress.a
    wph
    cA
    cS
    cF
    wf
    cA
    @46
    cF
    wf
    gsumress.f
    wph
    cS
    @46
    cF
    cA
    @83
    feq3d
    mpbid
    gsumval
    3eqtr4d
end
