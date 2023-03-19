include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "clsp.mm"
include "cli.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "wceq.mm"
include "wss.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "uzss.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "cr.mm"
include "cdm.mm"
include "ciin.mm"
include "crab.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "fvex.mm"
include "mptexf.mm"
include "a1i.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "cbvmptf.mm"
include "simpl.mm"
include "fveq2d.mm"
include "mpteq2dva.mm"
include "eleq1d.mm"
include "iinss1.mm"
include "adantl.mm"
include "adantr.mm"
include "sseldd.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "nfv.mm"
include "nfan.mm"
include "eqid.mm"
include "simpll.mm"
include "adantll.mm"
include "csalg.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "smff.mm"
include "wb.mm"
include "eliin.mm"
include "mpbid.mm"
include "simpr.mm"
include "rspa.mm"
include "ffvelrnd.mm"
include "cz.mm"
include "eluzelz.mm"
include "limsupequzmpt.mm"
include "eqeltrd.mm"
include "renepnfd.mm"
include "limsupubuzmpt.mm"
include "c0.mm"
include "wne.mm"
include "uzid2.mm"
include "ne0i.mm"
include "supxrre3rnmpt.mm"
include "mpbird.mm"
include "elrabd.mm"
include "cbvrabv.mm"
include "syl6eleq.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexd.mm"
include "rabexd.mm"
include "eleqtrrd.mm"
include "elexd.mm"
include "fvmptd3.mm"
include "eqtrd.mm"
include "mpteq2da.mm"
include "eluzelz2.mm"
include "supcnvlimsupmpt.mm"
include "eqbrtrd.mm"

theorem smflimsuplem5
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  let vk: setvar k
  assume smflimsuplem5.a: |- F/ n ph
  assume smflimsuplem5.b: |- F/ m ph
  assume smflimsuplem5.m: |- ( ph -> M e. ZZ )
  assume smflimsuplem5.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem5.s: |- ( ph -> S e. SAlg )
  assume smflimsuplem5.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsuplem5.e: |- E = ( n e. Z |-> { x e. |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem5.h: |- H = ( n e. Z |-> ( x e. ( E ` n ) |-> sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )
  assume smflimsuplem5.r: |- ( ph -> ( limsup ` ( m e. Z |-> ( ( F ` m ) ` X ) ) ) e. RR )
  assume smflimsuplem5.n: |- ( ph -> N e. Z )
  assume smflimsuplem5.x: |- ( ph -> X e. |^|_ m e. ( ZZ>= ` N ) dom ( F ` m ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint M m
  disjoint N m
  disjoint N n
  disjoint m n
  disjoint X m
  disjoint X n
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m x
  disjoint E y
  disjoint F y
  disjoint n y
  disjoint x y
  disjoint X y
  disjoint m y
  disjoint k x
  assert |- ( ph -> ( n e. ( ZZ>= ` N ) |-> ( ( H ` n ) ` X ) ) ~~> ( limsup ` ( m e. ( ZZ>= ` N ) |-> ( ( F ` m ) ` X ) ) ) )

  proof
    wph
    vn
    cN
    cuz
    cfv
    #
    cX
    vn
    cv
    #
    cH
    cfv
    #
    cfv
    #
    cmpt
    vn
    @0
    vm
    @1
    cuz
    cfv
    #
    cX
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    vm
    @0
    @7
    cmpt
    clsp
    cfv
    #
    cli
    wph
    vn
    @0
    @3
    @10
    smflimsuplem5.a
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @3
    cX
    vx
    @1
    cE
    cfv
    #
    vm
    @4
    vx
    cv
    #
    @6
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    cfv
    @10
    @13
    cX
    @2
    @20
    @13
    @1
    cZ
    wcel
    #
    @20
    cvv
    wcel
    #
    @2
    @20
    wceq
    wph
    @0
    cZ
    @1
    wph
    cN
    cZ
    wcel
    #
    @0
    cZ
    wss
    smflimsuplem5.n
    @23
    @0
    cM
    cuz
    cfv
    #
    cZ
    @23
    cN
    @24
    wcel
    #
    @0
    @24
    wss
    @23
    @25
    cZ
    @24
    cN
    smflimsuplem5.z
    eleq2i
    biimpi
    cM
    cN
    uzss
    syl
    smflimsuplem5.z
    syl6sseqr
    syl
    #
    sselda
    #
    @22
    @13
    vx
    @14
    @19
    vx
    @1
    cE
    vx
    cE
    vn
    cZ
    @19
    cr
    wcel
    #
    vx
    vm
    @4
    @6
    cdm
    #
    ciin
    #
    crab
    #
    cmpt
    smflimsuplem5.e
    vx
    vn
    cZ
    @31
    vx
    cZ
    nfcv
    @28
    vx
    @30
    nfrab1
    nfmpt
    nfcxfr
    vx
    @1
    nfcv
    nffv
    #
    @1
    cE
    fvex
    mptexf
    a1i
    vn
    cZ
    @20
    cvv
    cH
    smflimsuplem5.h
    fvmpt2
    syl2anc
    fveq1d
    @13
    vy
    cX
    vm
    @4
    vy
    cv
    #
    @6
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    @10
    @14
    @20
    cvv
    vx
    vy
    @14
    @19
    @37
    @32
    vy
    @14
    nfcv
    vy
    @19
    nfcv
    vx
    @37
    nfcv
    @15
    @33
    wceq
    #
    cxr
    @18
    @36
    clt
    @38
    @17
    @35
    @38
    vm
    @4
    @16
    @34
    @15
    @33
    @6
    fveq2
    mpteq2dv
    rneqd
    supeq1d
    cbvmptf
    @33
    cX
    wceq
    #
    cxr
    @36
    @9
    clt
    @39
    @35
    @8
    @39
    vm
    @4
    @34
    @7
    @39
    @5
    @4
    wcel
    #
    wa
    @33
    cX
    @6
    @39
    @40
    simpl
    fveq2d
    mpteq2dva
    rneqd
    supeq1d
    #
    @13
    cX
    @31
    @14
    @13
    cX
    @37
    cr
    wcel
    #
    vy
    @30
    crab
    @31
    @13
    @42
    @10
    cr
    wcel
    #
    vy
    cX
    @30
    @39
    @37
    @10
    cr
    @41
    eleq1d
    @13
    vm
    @0
    @29
    ciin
    #
    @30
    cX
    @12
    @44
    @30
    wss
    #
    wph
    @12
    @4
    @0
    wss
    @45
    cN
    @1
    uzss
    #
    vm
    @4
    @0
    @29
    iinss1
    syl
    adantl
    wph
    cX
    @44
    wcel
    #
    @12
    smflimsuplem5.x
    adantr
    sseldd
    @13
    @43
    @7
    @33
    cle
    wbr
    vm
    @4
    wral
    vy
    cr
    wrex
    @13
    vy
    @7
    vm
    @1
    @4
    wph
    @12
    vm
    smflimsuplem5.b
    @12
    vm
    nfv
    nfan
    #
    @4
    eqid
    #
    @13
    @40
    wa
    wph
    @5
    @0
    wcel
    #
    @7
    cr
    wcel
    wph
    @12
    @40
    simpll
    @12
    @40
    @50
    wph
    @12
    @4
    @0
    @5
    @46
    sselda
    adantll
    wph
    @50
    wa
    #
    @29
    cr
    cX
    @6
    @51
    @29
    cS
    @6
    wph
    cS
    csalg
    wcel
    @50
    smflimsuplem5.s
    adantr
    @51
    wph
    @5
    cZ
    wcel
    #
    @6
    cS
    csmblfn
    cfv
    #
    wcel
    wph
    @50
    simpl
    wph
    @0
    cZ
    @5
    @26
    sselda
    wph
    cZ
    @53
    @5
    cF
    smflimsuplem5.f
    ffvelrnda
    syl2anc
    @29
    eqid
    smff
    @51
    cX
    @29
    wcel
    #
    vm
    @0
    wral
    #
    @50
    @54
    wph
    @55
    @50
    wph
    @47
    @55
    smflimsuplem5.x
    wph
    @47
    @47
    @55
    wb
    smflimsuplem5.x
    vm
    cX
    @0
    @29
    @44
    eliin
    syl
    mpbid
    adantr
    wph
    @50
    simpr
    @54
    vm
    @0
    rspa
    syl2anc
    ffvelrnd
    #
    syl2anc
    #
    @13
    @8
    clsp
    cfv
    #
    @13
    @58
    vm
    cZ
    @7
    cmpt
    clsp
    cfv
    #
    cr
    @13
    @4
    cZ
    @7
    vm
    @1
    cM
    cr
    cvv
    @48
    @12
    @1
    cz
    wcel
    wph
    cN
    @1
    eluzelz
    adantl
    wph
    cM
    cz
    wcel
    @12
    smflimsuplem5.m
    adantr
    @49
    smflimsuplem5.z
    @57
    @7
    cvv
    wcel
    #
    @13
    @52
    wa
    cX
    @6
    fvex
    #
    a1i
    limsupequzmpt
    wph
    @59
    cr
    wcel
    @12
    smflimsuplem5.r
    adantr
    eqeltrd
    renepnfd
    limsupubuzmpt
    @13
    vm
    vy
    @4
    @7
    @48
    @12
    @4
    c0
    wne
    #
    wph
    @12
    @1
    @4
    wcel
    @62
    @1
    cN
    uzid2
    @4
    @1
    ne0i
    syl
    #
    adantl
    @57
    supxrre3rnmpt
    mpbird
    #
    elrabd
    @42
    @28
    vy
    vx
    @30
    @33
    @15
    wceq
    #
    @37
    @19
    cr
    @65
    cxr
    @36
    @18
    clt
    @65
    @35
    @17
    @65
    vm
    @4
    @34
    @16
    @65
    @40
    wa
    @33
    @15
    @6
    @65
    @40
    simpl
    fveq2d
    mpteq2dva
    rneqd
    supeq1d
    eleq1d
    cbvrabv
    syl6eleq
    @13
    @21
    @31
    cvv
    wcel
    @14
    @31
    wceq
    @27
    @13
    @28
    vx
    @30
    @31
    cvv
    @31
    eqid
    @12
    @30
    cvv
    wcel
    wph
    @12
    vm
    @4
    @29
    cvv
    @63
    @29
    cvv
    wcel
    #
    vm
    @4
    wral
    @12
    @66
    vm
    @4
    @6
    @5
    cF
    fvex
    dmex
    rgenw
    a1i
    iinexd
    adantl
    rabexd
    vn
    cZ
    @31
    cvv
    cE
    smflimsuplem5.e
    fvmpt2
    syl2anc
    eleqtrrd
    @13
    @10
    cr
    @64
    elexd
    fvmptd3
    eqtrd
    mpteq2da
    wph
    @7
    vm
    vn
    cN
    @0
    smflimsuplem5.b
    wph
    @23
    cN
    cz
    wcel
    smflimsuplem5.n
    cM
    cN
    cZ
    smflimsuplem5.z
    eluzelz2
    syl
    #
    @0
    eqid
    #
    @56
    wph
    @11
    @59
    cr
    wph
    @0
    cZ
    @7
    vm
    cN
    cM
    cvv
    cvv
    smflimsuplem5.b
    @67
    smflimsuplem5.m
    @68
    smflimsuplem5.z
    @60
    @51
    @61
    a1i
    @60
    wph
    @52
    wa
    @61
    a1i
    limsupequzmpt
    smflimsuplem5.r
    eqeltrd
    supcnvlimsupmpt
    eqbrtrd
end
