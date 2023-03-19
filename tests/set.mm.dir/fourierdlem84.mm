include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "fourierdlem14.mm"
include "cicc.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "readdcld.mm"
include "ffvelrnd.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "remulcld.mm"
include "recnd.mm"
include "fmptd.mm"
include "cc0.mm"
include "cfzo.mm"
include "cioo.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "reseq1d.mm"
include "ioossicc.mm"
include "cxr.mm"
include "rexrd.mm"
include "cfz.mm"
include "fourierdlem15.mm"
include "fourierdlem8.mm"
include "syl5ss.mm"
include "resmptd.mm"
include "eqtrd.mm"
include "wss.mm"
include "iccssred.mm"
include "elfzofz.mm"
include "adantl.mm"
include "sseldd.mm"
include "fzofzp1.mm"
include "ad2antrr.mm"
include "elioore.mm"
include "clt.mm"
include "cmin.mm"
include "addcomd.mm"
include "resubcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "npcand.mm"
include "3eqtrrd.mm"
include "wbr.mm"
include "fssd.mm"
include "ioogtlb.mm"
include "ltadd2dd.mm"
include "eqbrtrd.mm"
include "iooltub.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fvmptd.mm"
include "oveq2d.mm"
include "pncan3d.mm"
include "breqtrd.mm"
include "eliood.mm"
include "fvres.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "ioosscn.mm"
include "fourierdlem23.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "feqmptd.mm"
include "sseldi.mm"
include "sstrd.mm"
include "adantlr.mm"
include "cncfmptssg.mm"
include "mulcncf.mm"
include "climc.mm"
include "ioossre.mm"
include "gtned.mm"
include "eleqtrd.mm"
include "fourierdlem53.mm"
include "limcresi.mm"
include "cnlimci.mm"
include "mullimc.mm"
include "reseq1i.mm"
include "syl5req.mm"
include "ltned.mm"
include "fourierdlem69.mm"

theorem fourierdlem84
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vi: setvar i
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cL: class L
  let cM: class M
  let cO: class O
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem84.1: |- ( ph -> A e. RR )
  assume fourierdlem84.2: |- ( ph -> B e. RR )
  assume fourierdlem84.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem84.xre: |- ( ph -> X e. RR )
  assume fourierdlem84.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( A + X ) /\ ( p ` m ) = ( B + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem84.m: |- ( ph -> M e. NN )
  assume fourierdlem84.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem84.fcn: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) e. ( ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) -cn-> CC ) )
  assume fourierdlem84.r: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> R e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` i ) ) )
  assume fourierdlem84.l: |- ( ( ph /\ i e. ( 0 ..^ M ) ) -> L e. ( ( F |` ( ( V ` i ) (,) ( V ` ( i + 1 ) ) ) ) limCC ( V ` ( i + 1 ) ) ) )
  assume fourierdlem84.q: |- Q = ( i e. ( 0 ... M ) |-> ( ( V ` i ) - X ) )
  assume fourierdlem84.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem84.d: |- ( ph -> D e. ( RR -cn-> RR ) )
  assume fourierdlem84.g: |- G = ( s e. ( A [,] B ) |-> ( ( F ` ( X + s ) ) x. ( D ` s ) ) )

  disjoint A i
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint A s
  disjoint i s
  disjoint B i
  disjoint B m
  disjoint B p
  disjoint B s
  disjoint D s
  disjoint F s
  disjoint G i
  disjoint L s
  disjoint M i
  disjoint M s
  disjoint M m
  disjoint M p
  disjoint Q i
  disjoint Q s
  disjoint Q p
  disjoint R s
  disjoint V i
  disjoint V s
  disjoint V p
  disjoint X i
  disjoint X s
  disjoint X m
  disjoint X p
  disjoint i ph
  disjoint ph s
  disjoint M j
  disjoint i j
  disjoint j s
  disjoint Q j
  disjoint V j
  disjoint X j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> G e. L^1 )

  proof
    wph
    cA
    cB
    cO
    cQ
    cR
    vi
    cv
    #
    cQ
    cfv
    #
    cD
    cfv
    #
    cmul
    co
    #
    vi
    vm
    cG
    cL
    @0
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cD
    cfv
    #
    cmul
    co
    #
    cM
    vp
    fourierdlem84.o
    fourierdlem84.m
    wph
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    cO
    cV
    cX
    vp
    fourierdlem84.1
    fourierdlem84.2
    fourierdlem84.xre
    fourierdlem84.p
    fourierdlem84.o
    fourierdlem84.m
    fourierdlem84.v
    fourierdlem84.q
    fourierdlem14
    #
    wph
    vs
    cA
    cB
    cicc
    co
    #
    cX
    vs
    cv
    #
    caddc
    co
    #
    cF
    cfv
    #
    @10
    cD
    cfv
    #
    cmul
    co
    #
    cc
    cG
    wph
    @10
    @9
    wcel
    #
    wa
    #
    @14
    @16
    @12
    @13
    @16
    cr
    cr
    @11
    cF
    wph
    cr
    cr
    cF
    wf
    #
    @15
    fourierdlem84.f
    adantr
    @16
    cX
    @10
    wph
    cX
    cr
    wcel
    #
    @15
    fourierdlem84.xre
    adantr
    @16
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @15
    @10
    cr
    wcel
    #
    wph
    @19
    @15
    fourierdlem84.1
    adantr
    wph
    @20
    @15
    fourierdlem84.2
    adantr
    wph
    @15
    simpr
    cA
    cB
    @10
    eliccre
    syl3anc
    #
    readdcld
    ffvelrnd
    @16
    cr
    cr
    @10
    cD
    wph
    cr
    cr
    cD
    wf
    #
    @15
    wph
    cD
    cr
    cr
    ccncf
    co
    #
    wcel
    @23
    fourierdlem84.d
    cr
    cr
    cD
    cncff
    syl
    #
    adantr
    @22
    ffvelrnd
    remulcld
    recnd
    fourierdlem84.g
    fmptd
    wph
    @0
    cc0
    cM
    cfzo
    co
    wcel
    #
    wa
    #
    cG
    @1
    @5
    cioo
    co
    #
    cres
    #
    vs
    @28
    @14
    cmpt
    #
    @28
    cc
    ccncf
    co
    #
    @27
    @29
    vs
    @9
    @14
    cmpt
    #
    @28
    cres
    #
    @30
    @27
    cG
    @32
    @28
    cG
    @32
    wceq
    @27
    fourierdlem84.g
    a1i
    reseq1d
    @27
    vs
    @9
    @28
    @14
    @27
    @28
    @1
    @5
    cicc
    co
    @9
    @1
    @5
    ioossicc
    @27
    cA
    cB
    cQ
    @0
    cM
    wph
    cA
    cxr
    wcel
    @26
    wph
    cA
    fourierdlem84.1
    rexrd
    adantr
    wph
    cB
    cxr
    wcel
    @26
    wph
    cB
    fourierdlem84.2
    rexrd
    adantr
    wph
    cc0
    cM
    cfz
    co
    #
    @9
    cQ
    wf
    @26
    wph
    cA
    cB
    cO
    cQ
    vi
    vm
    cM
    vp
    fourierdlem84.o
    fourierdlem84.m
    @8
    fourierdlem15
    adantr
    #
    wph
    @26
    simpr
    fourierdlem8
    syl5ss
    #
    resmptd
    #
    eqtrd
    @27
    vs
    @12
    @13
    @28
    @27
    vs
    @28
    @12
    cmpt
    #
    vs
    @28
    @11
    cF
    @0
    cV
    cfv
    #
    @4
    cV
    cfv
    #
    cioo
    co
    #
    cres
    #
    cfv
    #
    cmpt
    @31
    @27
    vs
    @28
    @12
    @43
    @27
    @10
    @28
    wcel
    #
    wa
    #
    @43
    @12
    @45
    @11
    @41
    wcel
    @43
    @12
    wceq
    @45
    @39
    @40
    @11
    @27
    @39
    cxr
    wcel
    @44
    @27
    @39
    @27
    cA
    cX
    caddc
    co
    #
    cB
    cX
    caddc
    co
    #
    cicc
    co
    #
    cr
    @39
    wph
    @48
    cr
    wss
    @26
    wph
    @46
    @47
    wph
    cA
    cX
    fourierdlem84.1
    fourierdlem84.xre
    readdcld
    wph
    cB
    cX
    fourierdlem84.2
    fourierdlem84.xre
    readdcld
    iccssred
    adantr
    #
    @27
    @34
    @48
    @0
    cV
    wph
    @34
    @48
    cV
    wf
    @26
    wph
    @46
    @47
    cP
    cV
    vi
    vm
    cM
    vp
    fourierdlem84.p
    fourierdlem84.m
    fourierdlem84.v
    fourierdlem15
    adantr
    #
    @26
    @0
    @34
    wcel
    #
    wph
    @0
    cc0
    cM
    elfzofz
    adantl
    #
    ffvelrnd
    sseldd
    #
    rexrd
    adantr
    @27
    @40
    cxr
    wcel
    @44
    @27
    @40
    @27
    @48
    cr
    @40
    @49
    @27
    @34
    @48
    @4
    cV
    @50
    @26
    @4
    @34
    wcel
    wph
    cc0
    cM
    @0
    fzofzp1
    adantl
    #
    ffvelrnd
    sseldd
    #
    rexrd
    adantr
    @45
    cX
    @10
    wph
    @18
    @26
    @44
    fourierdlem84.xre
    ad2antrr
    #
    @44
    @21
    @27
    @10
    @1
    @5
    elioore
    #
    adantl
    #
    readdcld
    @45
    @39
    cX
    @1
    caddc
    co
    #
    @11
    clt
    @27
    @39
    @59
    wceq
    @44
    @27
    @59
    @1
    cX
    caddc
    co
    @39
    cX
    cmin
    co
    #
    cX
    caddc
    co
    @39
    @27
    cX
    @1
    wph
    cX
    cc
    wcel
    @26
    wph
    cX
    fourierdlem84.xre
    recnd
    adantr
    #
    @27
    @1
    @27
    @9
    cr
    @1
    wph
    @9
    cr
    wss
    @26
    wph
    cA
    cB
    fourierdlem84.1
    fourierdlem84.2
    iccssred
    adantr
    #
    @27
    @34
    @9
    @0
    cQ
    @35
    @52
    ffvelrnd
    sseldd
    #
    recnd
    #
    addcomd
    @27
    @1
    @60
    cX
    caddc
    @27
    @51
    @60
    cr
    wcel
    @1
    @60
    wceq
    @52
    @27
    @39
    cX
    @53
    wph
    @18
    @26
    fourierdlem84.xre
    adantr
    #
    resubcld
    vi
    @34
    @60
    cr
    cQ
    fourierdlem84.q
    fvmpt2
    syl2anc
    oveq1d
    @27
    @39
    cX
    @27
    @39
    @53
    recnd
    @61
    npcand
    3eqtrrd
    #
    adantr
    @45
    @1
    @10
    cX
    @27
    @1
    cr
    wcel
    @44
    @63
    adantr
    #
    @58
    @56
    @45
    @1
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @44
    @1
    @10
    clt
    wbr
    @27
    @68
    @44
    @27
    @1
    @63
    rexrd
    adantr
    #
    @27
    @69
    @44
    @27
    @5
    @27
    @34
    cr
    @4
    cQ
    @27
    @34
    @9
    cr
    cQ
    @35
    @62
    fssd
    @54
    ffvelrnd
    #
    rexrd
    adantr
    #
    @27
    @44
    simpr
    #
    @1
    @5
    @10
    ioogtlb
    syl3anc
    #
    ltadd2dd
    eqbrtrd
    @45
    @11
    cX
    @5
    caddc
    co
    #
    @40
    clt
    @45
    @10
    @5
    cX
    @58
    @27
    @5
    cr
    wcel
    @44
    @71
    adantr
    @56
    @45
    @68
    @69
    @44
    @10
    @5
    clt
    wbr
    @70
    @72
    @73
    @1
    @5
    @10
    iooltub
    syl3anc
    #
    ltadd2dd
    @27
    @75
    @40
    wceq
    @44
    @27
    @75
    cX
    @40
    cX
    cmin
    co
    #
    caddc
    co
    @40
    @27
    @5
    @77
    cX
    caddc
    @27
    vj
    @4
    vj
    cv
    #
    cV
    cfv
    #
    cX
    cmin
    co
    #
    @77
    @34
    cQ
    cr
    cQ
    vj
    @34
    @80
    cmpt
    #
    wceq
    @27
    cQ
    vi
    @34
    @60
    cmpt
    @81
    fourierdlem84.q
    vi
    vj
    @34
    @60
    @80
    @0
    @78
    wceq
    @39
    @79
    cX
    cmin
    @0
    @78
    cV
    fveq2
    oveq1d
    cbvmptv
    eqtri
    a1i
    @78
    @4
    wceq
    #
    @80
    @77
    wceq
    @27
    @82
    @79
    @40
    cX
    cmin
    @78
    @4
    cV
    fveq2
    oveq1d
    adantl
    @54
    @27
    @40
    cX
    @55
    @65
    resubcld
    fvmptd
    oveq2d
    @27
    cX
    @40
    @61
    @27
    @40
    @55
    recnd
    pncan3d
    eqtrd
    #
    adantr
    breqtrd
    eliood
    #
    @11
    @41
    cF
    fvres
    syl
    eqcomd
    mpteq2dva
    @27
    @41
    @28
    @42
    cX
    vs
    @41
    cc
    wss
    @27
    @39
    @40
    ioosscn
    a1i
    fourierdlem84.fcn
    @28
    cc
    wss
    @27
    @1
    @5
    ioosscn
    a1i
    @61
    @84
    fourierdlem23
    eqeltrd
    @27
    vs
    cr
    cc
    @28
    cc
    @13
    vs
    cr
    @13
    cmpt
    #
    @85
    eqid
    wph
    @85
    cr
    cc
    ccncf
    co
    #
    wcel
    @26
    wph
    @24
    @86
    @85
    cr
    cc
    wss
    cc
    cc
    wss
    #
    @24
    @86
    wss
    ax-resscn
    cc
    ssid
    #
    cr
    cr
    cc
    cncfss
    mp2an
    #
    wph
    @85
    cD
    @24
    wph
    cD
    @85
    wph
    vs
    cr
    cr
    cD
    @25
    feqmptd
    #
    eqcomd
    fourierdlem84.d
    eqeltrd
    sseldi
    adantr
    @27
    @28
    @9
    cr
    @36
    @62
    sstrd
    #
    @87
    @27
    @88
    a1i
    wph
    @44
    @13
    cc
    wcel
    @26
    wph
    @44
    wa
    #
    @13
    @92
    cr
    cr
    @10
    cD
    wph
    @23
    @44
    @25
    adantr
    @44
    @21
    wph
    @57
    adantl
    #
    ffvelrnd
    recnd
    adantlr
    #
    cncfmptssg
    mulcncf
    eqeltrd
    @27
    @3
    @30
    @1
    climc
    co
    @29
    @1
    climc
    co
    @27
    vs
    @28
    @12
    @13
    @1
    @38
    vs
    @28
    @13
    cmpt
    #
    @30
    cR
    @2
    @38
    eqid
    #
    @95
    eqid
    #
    @30
    eqid
    #
    wph
    @44
    @12
    cc
    wcel
    @26
    @92
    @12
    @92
    cr
    cr
    @11
    cF
    wph
    @17
    @44
    fourierdlem84.f
    adantr
    @92
    cX
    @10
    wph
    @18
    @44
    fourierdlem84.xre
    adantr
    @93
    readdcld
    ffvelrnd
    recnd
    adantlr
    #
    @94
    @27
    @28
    @41
    cR
    @1
    cF
    @38
    cX
    vs
    wph
    @17
    @26
    fourierdlem84.f
    adantr
    #
    @65
    @91
    @96
    @84
    @41
    cr
    wss
    @27
    @39
    @40
    ioossre
    a1i
    #
    @45
    @1
    @10
    @67
    @74
    gtned
    @27
    cR
    @42
    @39
    climc
    co
    @42
    @59
    climc
    co
    fourierdlem84.r
    @27
    @39
    @59
    @42
    climc
    @66
    oveq2d
    eleqtrd
    @64
    fourierdlem53
    @27
    @2
    @85
    @28
    cres
    #
    @1
    climc
    co
    #
    @95
    @1
    climc
    co
    @27
    @85
    @1
    climc
    co
    #
    @103
    @2
    @1
    @28
    @85
    limcresi
    @27
    @2
    cD
    @1
    climc
    co
    #
    @104
    @27
    cr
    @1
    cc
    cD
    wph
    cD
    @86
    wcel
    @26
    wph
    @24
    @86
    cD
    @89
    fourierdlem84.d
    sseldi
    adantr
    #
    @63
    cnlimci
    wph
    @105
    @104
    wceq
    @26
    wph
    cD
    @85
    @1
    climc
    @90
    oveq1d
    adantr
    eleqtrd
    sseldi
    @27
    @102
    @95
    @1
    climc
    @27
    vs
    cr
    @28
    @13
    @91
    resmptd
    #
    oveq1d
    eleqtrd
    mullimc
    @27
    @30
    @29
    @1
    climc
    @27
    @29
    @33
    @30
    cG
    @32
    @28
    fourierdlem84.g
    reseq1i
    @37
    syl5req
    #
    oveq1d
    eleqtrd
    @27
    @7
    @30
    @5
    climc
    co
    @29
    @5
    climc
    co
    @27
    vs
    @28
    @12
    @13
    @5
    @38
    @95
    @30
    cL
    @6
    @96
    @97
    @98
    @99
    @94
    @27
    @28
    @41
    cL
    @5
    cF
    @38
    cX
    vs
    @100
    @65
    @91
    @96
    @84
    @101
    @45
    @10
    @5
    @58
    @76
    ltned
    @27
    cL
    @42
    @40
    climc
    co
    @42
    @75
    climc
    co
    fourierdlem84.l
    @27
    @40
    @75
    @42
    climc
    @27
    @75
    @40
    @83
    eqcomd
    oveq2d
    eleqtrd
    @27
    @5
    @71
    recnd
    fourierdlem53
    @27
    @6
    @102
    @5
    climc
    co
    #
    @95
    @5
    climc
    co
    @27
    @85
    @5
    climc
    co
    #
    @109
    @6
    @5
    @28
    @85
    limcresi
    @27
    @6
    cD
    @5
    climc
    co
    #
    @110
    @27
    cr
    @5
    cc
    cD
    @106
    @71
    cnlimci
    wph
    @111
    @110
    wceq
    @26
    wph
    cD
    @85
    @5
    climc
    @90
    oveq1d
    adantr
    eleqtrd
    sseldi
    @27
    @102
    @95
    @5
    climc
    @107
    oveq1d
    eleqtrd
    mullimc
    @27
    @30
    @29
    @5
    climc
    @108
    oveq1d
    eleqtrd
    fourierdlem69
end
