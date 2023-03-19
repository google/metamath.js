include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "wcel.mm"
include "cdm.mm"
include "ciin.mm"
include "crab.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "eqid.mm"
include "wf.mm"
include "wss.mm"
include "syl6eleq.mm"
include "uzss.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "csalg.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "smff.mm"
include "syldan.mm"
include "iinss2.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "clsp.mm"
include "cpnf.mm"
include "nfmpt1.mm"
include "cz.mm"
include "eluzelz.mm"
include "fmptdf.mm"
include "ffnd.mm"
include "cvv.mm"
include "nfcv.mm"
include "fvexd.mm"
include "mptfnd.mm"
include "wceq.mm"
include "a1i.mm"
include "fvmpt2d.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "limsupequz.mm"
include "eqcomi.mm"
include "mpteq1i.mm"
include "fveq2i.mm"
include "eqtrd.mm"
include "renepnfd.mm"
include "eqnetrd.mm"
include "limsupubuzmpt.mm"
include "c0.mm"
include "wne.mm"
include "uzid.mm"
include "ne0i.mm"
include "3syl.mm"
include "supxrre3rnmpt.mm"
include "mpbird.mm"
include "jca.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "eleq2i.mm"
include "elrab.mm"
include "bitri.mm"
include "sylibr.mm"
include "id.mm"
include "nfrab1.mm"
include "nfmpt.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "fvex.mm"
include "mptexf.mm"
include "dmeqd.mm"
include "cbvmptf.mm"
include "xrltso.mm"
include "supex.mm"
include "dmmptd.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexd.mm"
include "rabexd.mm"
include "3eqtrrd.mm"
include "eleqtrd.mm"

theorem smflimsuplem2
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  let vk: setvar k
  assume smflimsuplem2.p: |- F/ m ph
  assume smflimsuplem2.m: |- ( ph -> M e. ZZ )
  assume smflimsuplem2.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem2.s: |- ( ph -> S e. SAlg )
  assume smflimsuplem2.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsuplem2.e: |- E = ( n e. Z |-> { x e. |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem2.h: |- H = ( n e. Z |-> ( x e. ( E ` n ) |-> sup ( ran ( m e. ( ZZ>= ` n ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )
  assume smflimsuplem2.n: |- ( ph -> n e. Z )
  assume smflimsuplem2.r: |- ( ph -> ( limsup ` ( m e. Z |-> ( ( F ` m ) ` X ) ) ) e. RR )
  assume smflimsuplem2.x: |- ( ph -> X e. |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) )

  disjoint F x
  disjoint M m
  disjoint X m
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint E y
  disjoint F y
  disjoint x y
  disjoint X y
  disjoint m y
  disjoint n y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> X e. dom ( H ` n ) )

  proof
    wph
    cX
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    vx
    cv
    #
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
    cr
    wcel
    #
    vx
    vm
    @1
    @4
    cdm
    #
    ciin
    #
    crab
    #
    @0
    cH
    cfv
    #
    cdm
    #
    wph
    cX
    @11
    wcel
    #
    vm
    @1
    cX
    @4
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
    cr
    wcel
    #
    wa
    #
    cX
    @12
    wcel
    #
    wph
    @15
    @20
    smflimsuplem2.x
    wph
    @20
    @16
    vy
    cv
    #
    cle
    wbr
    vm
    @1
    wral
    vy
    cr
    wrex
    wph
    vy
    @16
    vm
    @0
    @1
    smflimsuplem2.p
    @1
    eqid
    wph
    @3
    @1
    wcel
    #
    wa
    #
    @10
    cr
    cX
    @4
    wph
    @24
    @3
    cZ
    wcel
    #
    @10
    cr
    @4
    wf
    @25
    @1
    cZ
    @3
    wph
    @1
    cZ
    wss
    @24
    wph
    @1
    cM
    cuz
    cfv
    #
    cZ
    wph
    @0
    @27
    wcel
    #
    @1
    @27
    wss
    wph
    @0
    cZ
    @27
    smflimsuplem2.n
    smflimsuplem2.z
    syl6eleq
    #
    cM
    @0
    uzss
    syl
    smflimsuplem2.z
    syl6sseqr
    adantr
    wph
    @24
    simpr
    sseldd
    #
    wph
    @26
    wa
    @10
    cS
    @4
    wph
    cS
    csalg
    wcel
    @26
    smflimsuplem2.s
    adantr
    wph
    cZ
    cS
    csmblfn
    cfv
    @3
    cF
    smflimsuplem2.f
    ffvelrnda
    @10
    eqid
    smff
    syldan
    @25
    @11
    @10
    cX
    @24
    @11
    @10
    wss
    wph
    vm
    @1
    @10
    iinss2
    adantl
    wph
    @15
    @24
    smflimsuplem2.x
    adantr
    sseldd
    ffvelrnd
    #
    wph
    @17
    clsp
    cfv
    #
    vm
    cZ
    @16
    cmpt
    #
    clsp
    cfv
    #
    cpnf
    wph
    @32
    vm
    @27
    @16
    cmpt
    #
    clsp
    cfv
    #
    @34
    wph
    vm
    @17
    @35
    @0
    @0
    cM
    smflimsuplem2.p
    vm
    @1
    @16
    nfmpt1
    vm
    @27
    @16
    nfmpt1
    wph
    @28
    @0
    cz
    wcel
    #
    @29
    cM
    @0
    eluzelz
    syl
    #
    wph
    @1
    cr
    @17
    wph
    vm
    @1
    @16
    cr
    @17
    smflimsuplem2.p
    @31
    @17
    eqid
    #
    fmptdf
    ffnd
    smflimsuplem2.m
    wph
    vm
    @27
    @16
    cvv
    vm
    @27
    nfcv
    smflimsuplem2.p
    wph
    @3
    @27
    wcel
    #
    wa
    cX
    @4
    fvexd
    mptfnd
    @38
    @25
    @3
    @17
    cfv
    @16
    @3
    @35
    cfv
    #
    wph
    vm
    @1
    @16
    @17
    cvv
    @17
    @17
    wceq
    wph
    @39
    a1i
    @25
    cX
    @4
    fvexd
    #
    fvmpt2d
    @25
    @40
    @16
    cvv
    wcel
    @41
    @16
    wceq
    @25
    @3
    cZ
    @27
    @30
    smflimsuplem2.z
    syl6eleq
    @42
    vm
    @27
    @16
    cvv
    @35
    @35
    eqid
    fvmpt2
    syl2anc
    eqtr4d
    limsupequz
    @36
    @34
    wceq
    wph
    @35
    @33
    clsp
    vm
    @27
    cZ
    @16
    cZ
    @27
    smflimsuplem2.z
    eqcomi
    mpteq1i
    fveq2i
    a1i
    eqtrd
    wph
    @34
    smflimsuplem2.r
    renepnfd
    eqnetrd
    limsupubuzmpt
    wph
    vm
    vy
    @1
    @16
    smflimsuplem2.p
    wph
    @37
    @0
    @1
    wcel
    @1
    c0
    wne
    @38
    @0
    uzid
    @1
    @0
    ne0i
    3syl
    #
    @31
    supxrre3rnmpt
    mpbird
    jca
    @22
    cX
    vm
    @1
    @23
    @4
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
    cr
    wcel
    #
    vy
    @11
    crab
    #
    wcel
    @21
    @12
    @49
    cX
    @9
    @48
    vx
    vy
    @11
    @2
    @23
    wceq
    #
    @8
    @47
    cr
    @50
    cxr
    @7
    @46
    clt
    @50
    @6
    @45
    @50
    vm
    @1
    @5
    @44
    @2
    @23
    @4
    fveq2
    mpteq2dv
    rneqd
    supeq1d
    #
    eleq1d
    cbvrabv
    eleq2i
    @48
    @20
    vy
    cX
    @11
    @23
    cX
    wceq
    #
    @47
    @19
    cr
    @52
    cxr
    @46
    @18
    clt
    @52
    @45
    @17
    @52
    vm
    @1
    @44
    @16
    @23
    cX
    @4
    fveq2
    mpteq2dv
    rneqd
    supeq1d
    eleq1d
    elrab
    bitri
    sylibr
    wph
    @14
    vx
    @0
    cE
    cfv
    #
    @8
    cmpt
    #
    cdm
    @53
    @12
    wph
    @13
    @54
    wph
    wph
    @0
    cZ
    wcel
    #
    @13
    @54
    wceq
    wph
    id
    smflimsuplem2.n
    wph
    vn
    cZ
    @54
    cH
    cvv
    cH
    vn
    cZ
    @54
    cmpt
    wceq
    wph
    smflimsuplem2.h
    a1i
    @54
    cvv
    wcel
    wph
    @55
    wa
    vx
    @53
    @8
    vx
    @0
    cE
    vx
    cE
    vn
    cZ
    @12
    cmpt
    smflimsuplem2.e
    vx
    vn
    cZ
    @12
    vx
    cZ
    nfcv
    @9
    vx
    @11
    nfrab1
    nfmpt
    nfcxfr
    vx
    @0
    nfcv
    nffv
    #
    @0
    cE
    fvex
    mptexf
    a1i
    fvmpt2d
    syl2anc
    dmeqd
    wph
    vy
    @54
    @53
    @47
    cvv
    vx
    vy
    @53
    @8
    @47
    @56
    vy
    @53
    nfcv
    vy
    @8
    nfcv
    vx
    @47
    nfcv
    @51
    cbvmptf
    @47
    cvv
    wcel
    wph
    @23
    @53
    wcel
    wa
    cxr
    @46
    clt
    xrltso
    supex
    a1i
    dmmptd
    wph
    @55
    @12
    cvv
    wcel
    @53
    @12
    wceq
    smflimsuplem2.n
    wph
    @9
    vx
    @11
    @12
    cvv
    @12
    eqid
    wph
    vm
    @1
    @10
    cvv
    @43
    @10
    cvv
    wcel
    #
    vm
    @1
    wral
    wph
    @57
    vm
    @1
    @4
    @3
    cF
    fvex
    dmex
    rgenw
    a1i
    iinexd
    rabexd
    vn
    cZ
    @12
    cvv
    cE
    smflimsuplem2.e
    fvmpt2
    syl2anc
    3eqtrrd
    eleqtrd
end
