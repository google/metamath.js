include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cim.mm"
include "cv.mm"
include "wa.mm"
include "cvv.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "cz.mm"
include "adantr.mm"
include "cc.mm"
include "anassrs.mm"
include "mbfmptcl.mm"
include "an32s.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "wral.mm"
include "cr.mm"
include "simpr.mm"
include "recld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfv.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "climre.mm"
include "ismbfcn2.mm"
include "mpbid.mm"
include "simpld.mm"
include "anasss.mm"
include "mbflimlem.mm"
include "imcld.mm"
include "climim.mm"
include "simprd.mm"
include "cli.mm"
include "wbr.mm"
include "climcl.mm"
include "syl.mm"
include "mpbir2and.mm"

theorem mbflim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  assume mbflim.1: |- Z = ( ZZ>= ` M )
  assume mbflim.2: |- ( ph -> M e. ZZ )
  assume mbflim.4: |- ( ( ph /\ x e. A ) -> ( n e. Z |-> B ) ~~> C )
  assume mbflim.5: |- ( ( ph /\ n e. Z ) -> ( x e. A |-> B ) e. MblFn )
  assume mbflim.6: |- ( ( ph /\ ( n e. Z /\ x e. A ) ) -> B e. V )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint n ph
  disjoint ph x
  disjoint Z n
  disjoint Z x
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint C k
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint Z j
  disjoint Z k
  disjoint Z m
  disjoint Z y
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B y
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M y
  assert |- ( ph -> ( x e. A |-> C ) e. MblFn )

  proof
    wph
    vx
    cA
    cC
    cmpt
    cmbf
    wcel
    vx
    cA
    cC
    cre
    cfv
    #
    cmpt
    cmbf
    wcel
    vx
    cA
    cC
    cim
    cfv
    #
    cmpt
    cmbf
    wcel
    wph
    vx
    cA
    cB
    cre
    cfv
    #
    @0
    vn
    cM
    cZ
    mbflim.1
    mbflim.2
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    cC
    vk
    vn
    cZ
    cB
    cmpt
    #
    vn
    cZ
    @2
    cmpt
    #
    cM
    cvv
    cZ
    mbflim.1
    mbflim.4
    @6
    cvv
    wcel
    @4
    vn
    cZ
    @2
    cZ
    cM
    cuz
    cfv
    cvv
    mbflim.1
    cM
    cuz
    fvex
    eqeltri
    #
    mptex
    a1i
    wph
    cM
    cz
    wcel
    @3
    mbflim.2
    adantr
    #
    @4
    cZ
    cc
    vk
    cv
    #
    @5
    @4
    vn
    cZ
    cB
    cc
    @5
    wph
    vn
    cv
    #
    cZ
    wcel
    #
    @3
    cB
    cc
    wcel
    #
    wph
    @11
    wa
    #
    vx
    cA
    cB
    cV
    mbflim.5
    wph
    @11
    @3
    cB
    cV
    wcel
    mbflim.6
    anassrs
    mbfmptcl
    #
    an32s
    #
    @5
    eqid
    #
    fmptd
    ffvelrnda
    #
    @4
    @9
    @6
    cfv
    #
    @9
    @5
    cfv
    #
    cre
    cfv
    #
    wceq
    #
    vk
    cZ
    @4
    @10
    @6
    cfv
    #
    @10
    @5
    cfv
    #
    cre
    cfv
    #
    wceq
    #
    vn
    cZ
    wral
    @21
    vk
    cZ
    wral
    @4
    @25
    vn
    cZ
    @4
    @11
    wa
    #
    @22
    @2
    @24
    @26
    @11
    @2
    cr
    wcel
    @22
    @2
    wceq
    @4
    @11
    simpr
    #
    @26
    cB
    @15
    recld
    vn
    cZ
    @2
    cr
    @6
    @6
    eqid
    fvmpt2
    syl2anc
    @26
    @23
    cB
    cre
    @26
    @11
    @12
    @23
    cB
    wceq
    @27
    @15
    vn
    cZ
    cB
    cc
    @5
    @16
    fvmpt2
    syl2anc
    #
    fveq2d
    eqtr4d
    ralrimiva
    @21
    @25
    vk
    vn
    cZ
    vn
    @18
    @20
    vn
    cZ
    @2
    @9
    nffvmpt1
    vn
    @19
    cre
    vn
    cre
    nfcv
    vn
    cZ
    cB
    @9
    nffvmpt1
    #
    nffv
    nfeq
    @25
    vk
    nfv
    @9
    @10
    wceq
    #
    @18
    @22
    @20
    @24
    @9
    @10
    @6
    fveq2
    @30
    @19
    @23
    cre
    @9
    @10
    @5
    fveq2
    #
    fveq2d
    eqeq12d
    cbvral
    sylibr
    r19.21bi
    climre
    @13
    vx
    cA
    @2
    cmpt
    cmbf
    wcel
    #
    vx
    cA
    cB
    cim
    cfv
    #
    cmpt
    cmbf
    wcel
    #
    @13
    vx
    cA
    cB
    cmpt
    cmbf
    wcel
    @32
    @34
    wa
    mbflim.5
    @13
    vx
    cA
    cB
    @14
    ismbfcn2
    mpbid
    #
    simpld
    wph
    @11
    @3
    wa
    wa
    #
    cB
    wph
    @11
    @3
    @12
    @14
    anasss
    #
    recld
    mbflimlem
    wph
    vx
    cA
    @33
    @1
    vn
    cM
    cZ
    mbflim.1
    mbflim.2
    @4
    cC
    vk
    @5
    vn
    cZ
    @33
    cmpt
    #
    cM
    cvv
    cZ
    mbflim.1
    mbflim.4
    @38
    cvv
    wcel
    @4
    vn
    cZ
    @33
    @7
    mptex
    a1i
    @8
    @17
    @4
    @9
    @38
    cfv
    #
    @19
    cim
    cfv
    #
    wceq
    #
    vk
    cZ
    @4
    @10
    @38
    cfv
    #
    @23
    cim
    cfv
    #
    wceq
    #
    vn
    cZ
    wral
    @41
    vk
    cZ
    wral
    @4
    @44
    vn
    cZ
    @26
    @42
    @33
    @43
    @26
    @11
    @33
    cr
    wcel
    @42
    @33
    wceq
    @27
    @26
    cB
    @15
    imcld
    vn
    cZ
    @33
    cr
    @38
    @38
    eqid
    fvmpt2
    syl2anc
    @26
    @23
    cB
    cim
    @28
    fveq2d
    eqtr4d
    ralrimiva
    @41
    @44
    vk
    vn
    cZ
    vn
    @39
    @40
    vn
    cZ
    @33
    @9
    nffvmpt1
    vn
    @19
    cim
    vn
    cim
    nfcv
    @29
    nffv
    nfeq
    @44
    vk
    nfv
    @30
    @39
    @42
    @40
    @43
    @9
    @10
    @38
    fveq2
    @30
    @19
    @23
    cim
    @31
    fveq2d
    eqeq12d
    cbvral
    sylibr
    r19.21bi
    climim
    @13
    @32
    @34
    @35
    simprd
    @36
    cB
    @37
    imcld
    mbflimlem
    wph
    vx
    cA
    cC
    @4
    @5
    cC
    cli
    wbr
    cC
    cc
    wcel
    mbflim.4
    cC
    @5
    climcl
    syl
    ismbfcn2
    mpbir2and
end
