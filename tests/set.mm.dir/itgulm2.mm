include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "citg.mm"
include "cli.mm"
include "wbr.mm"
include "eqid.mm"
include "fmptd.mm"
include "iblulm.mm"
include "cv.mm"
include "cfv.mm"
include "itgulm.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nffv.mm"
include "nfitg.mm"
include "wceq.mm"
include "fveq2.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "cbvitg.mm"
include "fveq1d.mm"
include "adantr.mm"
include "itgeq2dv.mm"
include "syl5eq.mm"
include "cbvmpt.mm"
include "wa.mm"
include "cvv.mm"
include "simplr.mm"
include "culm.mm"
include "ulmscl.mm"
include "mptexg.mm"
include "3syl.mm"
include "ad2antrr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "cc.mm"
include "simpr.mm"
include "wf.mm"
include "wral.mm"
include "cmap.mm"
include "co.mm"
include "wfn.mm"
include "ralrimivw.mm"
include "fnmpt.mm"
include "syl.mm"
include "ulmf2.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "elmapi.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "ulmcl.mm"
include "3brtr3d.mm"
include "jca.mm"

theorem itgulm2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vn: setvar n
  let vz: setvar z
  assume itgulm2.z: |- Z = ( ZZ>= ` M )
  assume itgulm2.m: |- ( ph -> M e. ZZ )
  assume itgulm2.c: |- ( ( ph /\ k e. Z ) -> ( x e. S |-> A ) e. ( S -cn-> CC ) )
  assume itgulm2.l: |- ( ( ph /\ k e. Z ) -> ( x e. S |-> A ) e. L^1 )
  assume itgulm2.u: |- ( ph -> ( k e. Z |-> ( x e. S |-> A ) ) ( ~~>u ` S ) ( x e. S |-> B ) )
  assume itgulm2.s: |- ( ph -> ( vol ` S ) e. RR )

  disjoint k x
  disjoint k ph
  disjoint ph x
  disjoint S k
  disjoint S x
  disjoint Z k
  disjoint Z x
  disjoint n z
  disjoint A n
  disjoint A z
  disjoint k n
  disjoint k z
  disjoint n x
  disjoint n ph
  disjoint x z
  disjoint ph z
  disjoint S n
  disjoint S z
  disjoint Z n
  disjoint Z z
  disjoint B n
  disjoint B z
  disjoint M n
  disjoint M z
  assert |- ( ph -> ( ( x e. S |-> B ) e. L^1 /\ ( k e. Z |-> S. S A _d x ) ~~> S. S B _d x ) )

  proof
    wph
    vx
    cS
    cB
    cmpt
    #
    cibl
    wcel
    vk
    cZ
    vx
    cS
    cA
    citg
    #
    cmpt
    #
    vx
    cS
    cB
    citg
    #
    cli
    wbr
    wph
    cS
    vk
    cZ
    vx
    cS
    cA
    cmpt
    #
    cmpt
    #
    @0
    cM
    cZ
    itgulm2.z
    itgulm2.m
    wph
    vk
    cZ
    @4
    cibl
    @5
    itgulm2.l
    @5
    eqid
    #
    fmptd
    #
    itgulm2.u
    itgulm2.s
    iblulm
    wph
    vn
    cZ
    vz
    cS
    vz
    cv
    #
    vn
    cv
    #
    @5
    cfv
    #
    cfv
    #
    citg
    #
    cmpt
    #
    vz
    cS
    @8
    @0
    cfv
    #
    citg
    #
    @2
    @3
    cli
    wph
    vz
    cS
    vn
    @5
    @0
    cM
    cZ
    itgulm2.z
    itgulm2.m
    @7
    itgulm2.u
    itgulm2.s
    itgulm
    wph
    @13
    vk
    cZ
    vx
    cS
    vx
    cv
    #
    vk
    cv
    #
    @5
    cfv
    #
    cfv
    #
    citg
    #
    cmpt
    @2
    vn
    vk
    cZ
    @12
    @20
    vz
    vk
    cS
    @11
    vk
    cS
    nfcv
    vk
    @8
    @10
    vk
    cZ
    @4
    @9
    nffvmpt1
    vk
    @8
    nfcv
    nffv
    nfitg
    vn
    @20
    nfcv
    @9
    @17
    wceq
    #
    @12
    vx
    cS
    @16
    @10
    cfv
    #
    citg
    @20
    vz
    vx
    cS
    @11
    @22
    @8
    @16
    @10
    fveq2
    vx
    @8
    @10
    vx
    @9
    @5
    vx
    vk
    cZ
    @4
    vx
    cZ
    nfcv
    vx
    cS
    cA
    nfmpt1
    nfmpt
    vx
    @9
    nfcv
    nffv
    vx
    @8
    nfcv
    nffv
    vz
    @22
    nfcv
    cbvitg
    @21
    vx
    cS
    @22
    @19
    @21
    @22
    @19
    wceq
    @16
    cS
    wcel
    #
    @21
    @16
    @10
    @18
    @9
    @17
    @5
    fveq2
    fveq1d
    adantr
    itgeq2dv
    syl5eq
    cbvmpt
    wph
    vk
    cZ
    @20
    @1
    wph
    @17
    cZ
    wcel
    #
    wa
    #
    vx
    cS
    @19
    cA
    @25
    @23
    wa
    #
    @19
    @16
    @4
    cfv
    #
    cA
    @26
    @16
    @18
    @4
    @26
    @24
    @4
    cvv
    wcel
    #
    @18
    @4
    wceq
    wph
    @24
    @23
    simplr
    wph
    @28
    @24
    @23
    wph
    @5
    @0
    cS
    culm
    cfv
    wbr
    #
    cS
    cvv
    wcel
    @28
    itgulm2.u
    cS
    @5
    @0
    ulmscl
    vx
    cS
    cA
    cvv
    mptexg
    3syl
    #
    ad2antrr
    vk
    cZ
    @4
    cvv
    @5
    @6
    fvmpt2
    syl2anc
    fveq1d
    @26
    @23
    cA
    cc
    wcel
    #
    @27
    cA
    wceq
    @25
    @23
    simpr
    @25
    @31
    vx
    cS
    @25
    cS
    cc
    @4
    wf
    #
    @31
    vx
    cS
    wral
    @25
    @4
    cc
    cS
    cmap
    co
    #
    wcel
    #
    @32
    wph
    @34
    vk
    cZ
    wph
    cZ
    @33
    @5
    wf
    #
    @34
    vk
    cZ
    wral
    wph
    @5
    cZ
    wfn
    #
    @29
    @35
    wph
    @28
    vk
    cZ
    wral
    @36
    wph
    @28
    vk
    cZ
    @30
    ralrimivw
    vk
    cZ
    @4
    @5
    cvv
    @6
    fnmpt
    syl
    itgulm2.u
    cS
    @5
    @0
    cZ
    ulmf2
    syl2anc
    vk
    cZ
    @33
    @4
    @5
    @6
    fmpt
    sylibr
    r19.21bi
    @4
    cc
    cS
    elmapi
    syl
    vx
    cS
    cc
    cA
    @4
    @4
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    vx
    cS
    cA
    cc
    @4
    @37
    fvmpt2
    syl2anc
    eqtrd
    itgeq2dv
    mpteq2dva
    syl5eq
    wph
    @15
    vx
    cS
    @16
    @0
    cfv
    #
    citg
    @3
    vz
    vx
    cS
    @14
    @38
    @8
    @16
    @0
    fveq2
    vx
    cS
    cB
    @8
    nffvmpt1
    vz
    @38
    nfcv
    cbvitg
    wph
    vx
    cS
    @38
    cB
    wph
    @23
    wa
    @23
    cB
    cc
    wcel
    #
    @38
    cB
    wceq
    wph
    @23
    simpr
    wph
    @39
    vx
    cS
    wph
    cS
    cc
    @0
    wf
    #
    @39
    vx
    cS
    wral
    wph
    @29
    @40
    itgulm2.u
    cS
    @5
    @0
    ulmcl
    syl
    vx
    cS
    cc
    cB
    @0
    @0
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    vx
    cS
    cB
    cc
    @0
    @41
    fvmpt2
    syl2anc
    itgeq2dv
    syl5eq
    3brtr3d
    jca
end
