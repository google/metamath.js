include "cn0.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cvv.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cdm.mm"
include "crab.mm"
include "cmap.mm"
include "co.mm"
include "wal.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cram.mm"
include "cmpt2.mm"
include "df-ram.mm"
include "a1i.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "simplrr.mm"
include "dmeqd.mm"
include "simpll3.mm"
include "fdm.mm"
include "syl.mm"
include "eqtrd.mm"
include "simplrl.mm"
include "eqeq2d.mm"
include "rabbidv.mm"
include "vex.mm"
include "simpll1.mm"
include "hashbcval.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "raleqdv.mm"
include "simpr.mm"
include "3ad2ant3.mm"
include "sylan9eqr.mm"
include "ad2antrr.mm"
include "fveq1d.mm"
include "breq1d.mm"
include "oveq2d.mm"
include "eqeltrd.mm"
include "eqtr3d.mm"
include "sseq1d.mm"
include "rabss.mm"
include "wb.mm"
include "wfn.mm"
include "elmapi.mm"
include "ad3antlr.mm"
include "ffn.mm"
include "fniniseg.mm"
include "3syl.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "biimpar.mm"
include "elpwi.mm"
include "adantl.mm"
include "hashbcss.mm"
include "syl3anc.mm"
include "sselda.mm"
include "syldan.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "anassrs.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "bitr2d.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "rexeqbidv.mm"
include "bitrd.mm"
include "imbi2d.mm"
include "albidv.mm"
include "rabbidva.mm"
include "syl6eqr.mm"
include "infeq1d.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "fex.mm"
include "syl2anc.mm"
include "xrltso.mm"
include "infex.mm"
include "ovmpt2d.mm"

theorem ramval
  let vx: setvar x
  let cC: class C
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cV: class V
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  let vm: setvar m
  let vr: setvar r
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cN: class N
  assume ramval.c: |- C = ( a e. _V , i e. NN0 |-> { b e. ~P a | ( # ` b ) = i } )
  assume ramval.t: |- T = { n e. NN0 | A. s ( n <_ ( # ` s ) -> A. f e. ( R ^m ( s C M ) ) E. c e. R E. x e. ~P s ( ( F ` c ) <_ ( # ` x ) /\ ( x C M ) C_ ( `' f " { c } ) ) ) }

  disjoint c f
  disjoint c x
  disjoint C c
  disjoint f x
  disjoint C f
  disjoint C x
  disjoint c n
  disjoint c s
  disjoint F c
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint n s
  disjoint n x
  disjoint F n
  disjoint s x
  disjoint F s
  disjoint F x
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a i
  disjoint a n
  disjoint a s
  disjoint a x
  disjoint M a
  disjoint b c
  disjoint b f
  disjoint b i
  disjoint b n
  disjoint b s
  disjoint b x
  disjoint M b
  disjoint c i
  disjoint M c
  disjoint f i
  disjoint M f
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint M i
  disjoint M n
  disjoint M s
  disjoint M x
  disjoint R c
  disjoint R f
  disjoint R n
  disjoint R s
  disjoint R x
  disjoint V c
  disjoint V f
  disjoint V n
  disjoint V s
  disjoint V x
  disjoint c y
  disjoint f y
  disjoint x y
  disjoint C y
  disjoint c m
  disjoint c r
  disjoint c z
  disjoint f m
  disjoint f r
  disjoint f z
  disjoint m n
  disjoint m r
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n r
  disjoint n y
  disjoint n z
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint s y
  disjoint s z
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint a m
  disjoint a r
  disjoint a y
  disjoint a z
  disjoint b m
  disjoint b r
  disjoint b y
  disjoint b z
  disjoint i m
  disjoint i r
  disjoint i y
  disjoint i z
  disjoint M m
  disjoint M r
  disjoint M y
  disjoint M z
  disjoint A a
  disjoint A i
  disjoint A x
  disjoint B a
  disjoint B i
  disjoint B x
  disjoint R m
  disjoint R r
  disjoint R y
  disjoint R z
  disjoint T m
  disjoint T r
  disjoint T y
  disjoint T z
  disjoint N a
  disjoint N i
  disjoint N x
  disjoint V m
  disjoint V r
  disjoint V y
  disjoint V z
  assert |- ( ( M e. NN0 /\ R e. V /\ F : R --> NN0 ) -> ( M Ramsey F ) = inf ( T , RR* , < ) )

  proof
    cM
    cn0
    wcel
    #
    cR
    cV
    wcel
    #
    cR
    cn0
    cF
    wf
    #
    w3a
    #
    vm
    vr
    cM
    cF
    cn0
    cvv
    vn
    cv
    #
    vs
    cv
    #
    chash
    cfv
    cle
    wbr
    #
    vc
    cv
    #
    vr
    cv
    #
    cfv
    #
    vx
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vy
    cv
    #
    chash
    cfv
    #
    vm
    cv
    #
    wceq
    #
    @13
    vf
    cv
    #
    cfv
    @7
    wceq
    #
    wi
    #
    vy
    @10
    cpw
    #
    wral
    #
    wa
    #
    vx
    @5
    cpw
    #
    wrex
    #
    vc
    @8
    cdm
    #
    wrex
    #
    vf
    @25
    @16
    vy
    @23
    crab
    #
    cmap
    co
    #
    wral
    #
    wi
    #
    vs
    wal
    #
    vn
    cn0
    crab
    #
    cxr
    clt
    cinf
    #
    cT
    cxr
    clt
    cinf
    #
    cram
    cvv
    cram
    vm
    vr
    cn0
    cvv
    @33
    cmpt2
    wceq
    @3
    vx
    vy
    vf
    vm
    vn
    vs
    vr
    vc
    df-ram
    a1i
    @3
    @15
    cM
    wceq
    #
    @8
    cF
    wceq
    #
    wa
    #
    wa
    #
    cxr
    @32
    cT
    clt
    @38
    @32
    @6
    @7
    cF
    cfv
    #
    @11
    cle
    wbr
    #
    @10
    cM
    cC
    co
    #
    @17
    ccnv
    @7
    csn
    cima
    #
    wss
    #
    wa
    #
    vx
    @23
    wrex
    #
    vc
    cR
    wrex
    #
    vf
    cR
    @5
    cM
    cC
    co
    #
    cmap
    co
    #
    wral
    #
    wi
    #
    vs
    wal
    #
    vn
    cn0
    crab
    cT
    @38
    @31
    @51
    vn
    cn0
    @38
    @4
    cn0
    wcel
    #
    wa
    #
    @30
    @50
    vs
    @53
    @29
    @49
    @6
    @53
    @29
    @26
    vf
    @48
    wral
    @49
    @53
    @26
    vf
    @28
    @48
    @53
    @25
    cR
    @27
    @47
    cmap
    @53
    @25
    cF
    cdm
    #
    cR
    @53
    @8
    cF
    @3
    @35
    @36
    @52
    simplrr
    #
    dmeqd
    @53
    @2
    @54
    cR
    wceq
    #
    @0
    @1
    @2
    @37
    @52
    simpll3
    cR
    cn0
    cF
    fdm
    #
    syl
    eqtrd
    @53
    @27
    @14
    cM
    wceq
    #
    vy
    @23
    crab
    #
    @47
    @53
    @16
    @58
    vy
    @23
    @53
    @15
    cM
    @14
    @3
    @35
    @36
    @52
    simplrl
    #
    eqeq2d
    rabbidv
    @53
    @5
    cvv
    wcel
    #
    @0
    @47
    @59
    wceq
    vs
    vex
    #
    @0
    @1
    @2
    @37
    @52
    simpll1
    #
    vy
    @5
    cC
    vi
    cM
    cvv
    va
    vb
    ramval.c
    hashbcval
    sylancr
    eqtr4d
    oveq12d
    raleqdv
    @53
    @26
    @46
    vf
    @48
    @53
    @17
    @48
    wcel
    #
    wa
    #
    @24
    @45
    vc
    @25
    cR
    @38
    @25
    cR
    wceq
    @52
    @64
    @37
    @3
    @25
    @54
    cR
    @37
    @8
    cF
    @35
    @36
    simpr
    dmeqd
    @2
    @0
    @56
    @1
    @57
    3ad2ant3
    sylan9eqr
    ad2antrr
    @65
    @22
    @44
    vx
    @23
    @65
    @10
    @23
    wcel
    #
    wa
    #
    @12
    @40
    @21
    @43
    @67
    @9
    @39
    @11
    cle
    @67
    @7
    @8
    cF
    @53
    @36
    @64
    @66
    @55
    ad2antrr
    fveq1d
    breq1d
    @67
    @43
    @16
    vy
    @20
    crab
    #
    @42
    wss
    #
    @21
    @67
    @41
    @68
    @42
    @67
    @10
    @15
    cC
    co
    #
    @41
    @68
    @67
    @15
    cM
    @10
    cC
    @53
    @35
    @64
    @66
    @60
    ad2antrr
    #
    oveq2d
    @67
    @10
    cvv
    wcel
    @15
    cn0
    wcel
    @70
    @68
    wceq
    vx
    vex
    @67
    @15
    cM
    cn0
    @71
    @53
    @0
    @64
    @66
    @63
    ad2antrr
    #
    eqeltrd
    vy
    @10
    cC
    vi
    @15
    cvv
    va
    vb
    ramval.c
    hashbcval
    sylancr
    eqtr3d
    #
    sseq1d
    @69
    @16
    @13
    @42
    wcel
    #
    wi
    #
    vy
    @20
    wral
    @67
    @21
    @16
    vy
    @20
    @42
    rabss
    @67
    @75
    @19
    vy
    @20
    @67
    @13
    @20
    wcel
    #
    wa
    @16
    @74
    @18
    @67
    @76
    @16
    @74
    @18
    wb
    @67
    @76
    @16
    wa
    #
    wa
    #
    @74
    @13
    @47
    wcel
    #
    @18
    wa
    #
    @18
    @78
    @47
    cR
    @17
    wf
    #
    @17
    @47
    wfn
    @74
    @80
    wb
    @64
    @81
    @53
    @66
    @77
    @17
    cR
    @47
    elmapi
    ad3antlr
    @47
    cR
    @17
    ffn
    @47
    @7
    @13
    @17
    fniniseg
    3syl
    @78
    @79
    @18
    @67
    @77
    @13
    @41
    wcel
    #
    @79
    @67
    @82
    @77
    @67
    @82
    @13
    @68
    wcel
    @77
    @67
    @41
    @68
    @13
    @73
    eleq2d
    @16
    vy
    @20
    rabid
    syl6bb
    biimpar
    @67
    @41
    @47
    @13
    @67
    @61
    @10
    @5
    wss
    #
    @0
    @41
    @47
    wss
    @61
    @67
    @62
    a1i
    @66
    @83
    @65
    @10
    @5
    elpwi
    adantl
    @72
    @5
    @10
    cC
    vi
    cM
    cvv
    va
    vb
    ramval.c
    hashbcss
    syl3anc
    sselda
    syldan
    biantrurd
    bitr4d
    anassrs
    pm5.74da
    ralbidva
    syl5bb
    bitr2d
    anbi12d
    rexbidva
    rexeqbidv
    ralbidva
    bitrd
    imbi2d
    albidv
    rabbidva
    ramval.t
    syl6eqr
    infeq1d
    @0
    @1
    @2
    simp1
    @3
    @2
    @1
    cF
    cvv
    wcel
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    cR
    cn0
    cV
    cF
    fex
    syl2anc
    @34
    cvv
    wcel
    @3
    cxr
    cT
    clt
    xrltso
    infex
    a1i
    ovmpt2d
end
