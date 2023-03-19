include "cv.mm"
include "caddc.mm"
include "cseq.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cz.mm"
include "wcel.mm"
include "cli.mm"
include "cdm.mm"
include "cc.mm"
include "wa.mm"
include "recnd.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "climbdd.mm"
include "syl3anc.mm"
include "cof.mm"
include "adantr.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wfn.mm"
include "culm.mm"
include "cuz.mm"
include "seqfn.mm"
include "syl.mm"
include "fneq2i.mm"
include "sylibr.mm"
include "ulmf2.mm"
include "syl2anc.mm"
include "simplrl.mm"
include "cfz.mm"
include "csu.mm"
include "cmpt.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ad3antrrr.mm"
include "feqmptd.mm"
include "elmapi.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "simplr.mm"
include "syl6eleq.mm"
include "wss.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "ssriv.mm"
include "a1i.mm"
include "anasss.mm"
include "seqof2.mm"
include "ffvelrnd.mm"
include "fmptd.mm"
include "sylan2.mm"
include "eqeltrrd.mm"
include "fsumser.mm"
include "3eqtr4d.mm"
include "fveq2d.mm"
include "fzfid.mm"
include "fsumcl.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "fsumabs.mm"
include "simp-4l.mm"
include "syl12anc.mm"
include "fsumle.mm"
include "leabsd.mm"
include "eqidd.mm"
include "simprr.mm"
include "breq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "eqbrtrd.mm"
include "letrd.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "ulmbdd.mm"
include "rexlimddv.mm"

theorem mtestbdd
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vr: setvar r
  let vm: setvar m
  let vy: setvar y
  assume mtest.z: |- Z = ( ZZ>= ` N )
  assume mtest.n: |- ( ph -> N e. ZZ )
  assume mtest.s: |- ( ph -> S e. V )
  assume mtest.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume mtest.m: |- ( ph -> M e. W )
  assume mtest.c: |- ( ( ph /\ k e. Z ) -> ( M ` k ) e. RR )
  assume mtest.l: |- ( ( ph /\ ( k e. Z /\ z e. S ) ) -> ( abs ` ( ( F ` k ) ` z ) ) <_ ( M ` k ) )
  assume mtest.d: |- ( ph -> seq N ( + , M ) e. dom ~~> )
  assume mtest.t: |- ( ph -> seq N ( oF + , F ) ( ~~>u ` S ) T )

  disjoint k x
  disjoint k z
  disjoint F k
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint M k
  disjoint M x
  disjoint M z
  disjoint N k
  disjoint N x
  disjoint N z
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint T x
  disjoint T z
  disjoint Z k
  disjoint Z x
  disjoint Z z
  disjoint S k
  disjoint S x
  disjoint S z
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i x
  disjoint i z
  disjoint F i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k n
  disjoint k r
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint F n
  disjoint r x
  disjoint r z
  disjoint F r
  disjoint i m
  disjoint i y
  disjoint M i
  disjoint j m
  disjoint j y
  disjoint M j
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n y
  disjoint M n
  disjoint r y
  disjoint M r
  disjoint x y
  disjoint y z
  disjoint M y
  disjoint N i
  disjoint N j
  disjoint N m
  disjoint N n
  disjoint N r
  disjoint N y
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph y
  disjoint T n
  disjoint T y
  disjoint Z i
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z r
  disjoint Z y
  disjoint S i
  disjoint S j
  disjoint S n
  disjoint S r
  disjoint S y
  assert |- ( ph -> E. x e. RR A. z e. S ( abs ` ( T ` z ) ) <_ x )

  proof
    wph
    vm
    cv
    #
    caddc
    cM
    cN
    cseq
    #
    cfv
    #
    cabs
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    vz
    cv
    #
    cT
    cfv
    cabs
    cfv
    vx
    cv
    #
    cle
    wbr
    vz
    cS
    wral
    vx
    cr
    wrex
    vy
    cr
    wph
    cN
    cz
    wcel
    #
    @1
    cli
    cdm
    wcel
    @2
    cc
    wcel
    #
    vm
    cZ
    wral
    @6
    vy
    cr
    wrex
    mtest.n
    mtest.d
    wph
    @10
    vm
    cZ
    wph
    cZ
    cc
    @0
    @1
    wph
    vk
    cM
    cN
    cZ
    mtest.z
    mtest.n
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    @11
    cM
    cfv
    #
    mtest.c
    recnd
    #
    serf
    ffvelrnda
    ralrimiva
    vy
    vm
    @1
    cN
    cZ
    mtest.z
    climbdd
    syl3anc
    wph
    @4
    cr
    wcel
    #
    @6
    wa
    #
    wa
    #
    vx
    vz
    cS
    vn
    caddc
    cof
    #
    cF
    cN
    cseq
    #
    cT
    cN
    cZ
    mtest.z
    wph
    @9
    @16
    mtest.n
    adantr
    wph
    cZ
    cc
    cS
    cmap
    co
    #
    @19
    wf
    #
    @16
    wph
    @19
    cZ
    wfn
    #
    @19
    cT
    cS
    culm
    cfv
    wbr
    #
    @21
    wph
    @19
    cN
    cuz
    cfv
    #
    wfn
    #
    @22
    wph
    @9
    @25
    mtest.n
    @18
    cF
    cN
    seqfn
    syl
    cZ
    @24
    @19
    mtest.z
    fneq2i
    sylibr
    mtest.t
    cS
    @19
    cT
    cZ
    ulmf2
    syl2anc
    adantr
    @17
    vn
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @15
    @7
    @26
    @19
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    @4
    cle
    wbr
    #
    vz
    cS
    wral
    #
    @31
    @8
    cle
    wbr
    #
    vz
    cS
    wral
    #
    vx
    cr
    wrex
    wph
    @15
    @6
    @27
    simplrl
    #
    @28
    @32
    vz
    cS
    @28
    @7
    cS
    wcel
    #
    wa
    #
    @31
    cN
    @26
    cfz
    co
    #
    @7
    @11
    cF
    cfv
    #
    cfv
    #
    vk
    csu
    #
    cabs
    cfv
    #
    @4
    cle
    @38
    @30
    @42
    cabs
    @38
    @7
    vx
    cS
    @26
    caddc
    vj
    cZ
    @8
    vj
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cN
    cseq
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    @26
    caddc
    vj
    cZ
    @7
    @45
    cfv
    #
    cmpt
    #
    cN
    cseq
    #
    cfv
    #
    @30
    @42
    @37
    @51
    @55
    wceq
    @28
    vx
    @7
    @49
    @55
    cS
    @50
    vx
    vz
    weq
    #
    @26
    @48
    @54
    @56
    @47
    @53
    caddc
    cN
    @56
    vj
    cZ
    @46
    @52
    @8
    @7
    @45
    fveq2
    mpteq2dv
    seqeq3d
    fveq1d
    @50
    eqid
    @26
    @54
    fvex
    fvmpt
    adantl
    @38
    @7
    @29
    @50
    @38
    @29
    @26
    @18
    vj
    cZ
    vx
    cS
    @46
    cmpt
    #
    cmpt
    #
    cN
    cseq
    #
    cfv
    @50
    @38
    @26
    @19
    @59
    @38
    cF
    @58
    @18
    cN
    @38
    cF
    vj
    cZ
    @45
    cmpt
    @58
    @38
    vj
    cZ
    @20
    cF
    wph
    cZ
    @20
    cF
    wf
    @16
    @27
    @37
    mtest.f
    ad3antrrr
    #
    feqmptd
    @38
    vj
    cZ
    @45
    @57
    @38
    @44
    cZ
    wcel
    #
    wa
    #
    vx
    cS
    cc
    @45
    @62
    @45
    @20
    wcel
    cS
    cc
    @45
    wf
    @38
    cZ
    @20
    @44
    cF
    @60
    ffvelrnda
    @45
    cc
    cS
    elmapi
    syl
    #
    feqmptd
    mpteq2dva
    eqtrd
    seqeq3d
    fveq1d
    @38
    vj
    vx
    cS
    cZ
    caddc
    cN
    @26
    cV
    cc
    @46
    wph
    cS
    cV
    wcel
    @16
    @27
    @37
    mtest.s
    ad3antrrr
    @38
    @26
    cZ
    @24
    @17
    @27
    @37
    simplr
    mtest.z
    syl6eleq
    #
    @39
    cZ
    wss
    @38
    vk
    @39
    cZ
    @11
    @39
    wcel
    #
    @11
    @24
    cZ
    @11
    cN
    @26
    elfzuz
    mtest.z
    syl6eleqr
    #
    ssriv
    a1i
    @38
    @61
    @8
    cS
    wcel
    @46
    cc
    wcel
    @62
    cS
    cc
    @8
    @45
    @63
    ffvelrnda
    anasss
    seqof2
    eqtrd
    fveq1d
    @38
    @41
    vk
    @53
    cN
    @26
    @38
    @65
    wa
    #
    @12
    @11
    @53
    cfv
    #
    @41
    wceq
    @65
    @12
    @38
    @66
    adantl
    #
    vj
    @11
    @52
    @41
    cZ
    @53
    vj
    vk
    weq
    @7
    @45
    @40
    @44
    @11
    cF
    fveq2
    fveq1d
    @53
    eqid
    #
    @7
    @40
    fvex
    fvmpt
    syl
    #
    @64
    @67
    @68
    @41
    cc
    @71
    @65
    @38
    @12
    @68
    cc
    wcel
    @66
    @38
    cZ
    cc
    @11
    @53
    @38
    vj
    cZ
    @52
    cc
    @53
    @62
    cS
    cc
    @7
    @45
    @63
    @28
    @37
    @61
    simplr
    ffvelrnd
    @70
    fmptd
    ffvelrnda
    sylan2
    eqeltrrd
    #
    fsumser
    3eqtr4d
    fveq2d
    @38
    @43
    @39
    @41
    cabs
    cfv
    #
    vk
    csu
    #
    @4
    @38
    @42
    @38
    @39
    @41
    vk
    @38
    cN
    @26
    fzfid
    #
    @72
    fsumcl
    abscld
    @38
    @39
    @73
    vk
    @75
    @67
    @41
    @72
    abscld
    #
    fsumrecl
    #
    @28
    @15
    @37
    @36
    adantr
    #
    @38
    @39
    @41
    vk
    @75
    @72
    fsumabs
    @38
    @74
    @39
    @13
    vk
    csu
    #
    @4
    @77
    @38
    @39
    @13
    vk
    @75
    @67
    wph
    @12
    @13
    cr
    wcel
    wph
    @16
    @27
    @37
    @65
    simp-4l
    #
    @69
    mtest.c
    syl2anc
    #
    fsumrecl
    #
    @78
    @38
    @39
    @73
    @13
    vk
    @75
    @76
    @81
    @67
    wph
    @12
    @37
    @73
    @13
    cle
    wbr
    @80
    @69
    @28
    @37
    @65
    simplr
    mtest.l
    syl12anc
    fsumle
    @38
    @79
    @79
    cabs
    cfv
    #
    @4
    @82
    @38
    @79
    @38
    @79
    @82
    recnd
    abscld
    @78
    @38
    @79
    @82
    leabsd
    @38
    @83
    @26
    @1
    cfv
    #
    cabs
    cfv
    #
    @4
    cle
    @38
    @79
    @84
    cabs
    @38
    @13
    vk
    cM
    cN
    @26
    @67
    @13
    eqidd
    @64
    @67
    wph
    @12
    @13
    cc
    wcel
    @80
    @69
    @14
    syl2anc
    fsumser
    fveq2d
    @28
    @85
    @4
    cle
    wbr
    #
    @37
    @17
    @6
    @27
    @86
    wph
    @15
    @6
    simprr
    @5
    @86
    vm
    @26
    cZ
    vm
    vn
    weq
    #
    @3
    @85
    @4
    cle
    @87
    @2
    @84
    cabs
    @0
    @26
    @1
    fveq2
    fveq2d
    breq1d
    rspccva
    sylan
    adantr
    eqbrtrd
    letrd
    letrd
    letrd
    eqbrtrd
    ralrimiva
    @35
    @33
    vx
    @4
    cr
    vx
    vy
    weq
    @34
    @32
    vz
    cS
    @8
    @4
    @31
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    wph
    @23
    @16
    mtest.t
    adantr
    ulmbdd
    rexlimddv
end
