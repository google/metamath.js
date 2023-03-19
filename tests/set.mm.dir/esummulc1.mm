include "cesum.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cxmu.mm"
include "cmpt.mm"
include "cfv.mm"
include "cle.mm"
include "cordt.mm"
include "crest.mm"
include "eqid.mm"
include "xrge0mulc1cn.mm"
include "eqidd.mm"
include "wceq.mm"
include "oveq1.mm"
include "cxr.mm"
include "wcel.mm"
include "cico.mm"
include "icossxr.mm"
include "sseldi.mm"
include "xmul02.mm"
include "syl.mm"
include "sylan9eqr.mm"
include "0e0iccpnf.mm"
include "a1i.mm"
include "fvmptd.mm"
include "w3a.mm"
include "cxad.mm"
include "simp2.mm"
include "simp3.mm"
include "icossicc.mm"
include "3ad2ant1.mm"
include "xrge0adddir.mm"
include "syl3anc.mm"
include "cvv.mm"
include "wa.mm"
include "simpr.mm"
include "oveq1d.mm"
include "ge0xaddcl.mm"
include "3adant1.mm"
include "ovexd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "esumcocn.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "esumeq2dv.mm"
include "3eqtr3d.mm"

theorem esummulc1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vz: setvar z
  let vx: setvar x
  let vy: setvar y
  assume esummulc2.a: |- ( ph -> A e. V )
  assume esummulc2.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esummulc2.c: |- ( ph -> C e. ( 0 [,) +oo ) )

  disjoint A k
  disjoint C k
  disjoint V k
  disjoint k ph
  disjoint k z
  disjoint A z
  disjoint B z
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( sum* k e. A B *e C ) = sum* k e. A ( B *e C ) )

  proof
    wph
    cA
    cB
    vk
    cesum
    #
    vz
    cc0
    cpnf
    cicc
    co
    #
    vz
    cv
    #
    cC
    cxmu
    co
    #
    cmpt
    #
    cfv
    cA
    cB
    @4
    cfv
    #
    vk
    cesum
    @0
    cC
    cxmu
    co
    #
    cA
    cB
    cC
    cxmu
    co
    #
    vk
    cesum
    wph
    vx
    vy
    cA
    cB
    @4
    vk
    cle
    cordt
    cfv
    @1
    crest
    co
    #
    cV
    @8
    eqid
    #
    esummulc2.a
    esummulc2.b
    wph
    vz
    cC
    @4
    @8
    @9
    @4
    eqid
    esummulc2.c
    xrge0mulc1cn
    wph
    vz
    cc0
    @3
    cc0
    @1
    @4
    @1
    wph
    @4
    eqidd
    #
    @2
    cc0
    wceq
    wph
    @3
    cc0
    cC
    cxmu
    co
    #
    cc0
    @2
    cc0
    cC
    cxmu
    oveq1
    wph
    cC
    cxr
    wcel
    @11
    cc0
    wceq
    wph
    cc0
    cpnf
    cico
    co
    #
    cxr
    cC
    cc0
    cpnf
    icossxr
    esummulc2.c
    sseldi
    cC
    xmul02
    syl
    sylan9eqr
    cc0
    @1
    wcel
    wph
    0e0iccpnf
    a1i
    #
    @13
    fvmptd
    wph
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    w3a
    #
    @14
    @16
    cxad
    co
    #
    cC
    cxmu
    co
    #
    @14
    cC
    cxmu
    co
    #
    @16
    cC
    cxmu
    co
    #
    cxad
    co
    #
    @19
    @4
    cfv
    @14
    @4
    cfv
    #
    @16
    @4
    cfv
    #
    cxad
    co
    @18
    @15
    @17
    cC
    @1
    wcel
    @20
    @23
    wceq
    wph
    @15
    @17
    simp2
    #
    wph
    @15
    @17
    simp3
    #
    @18
    @12
    @1
    cC
    cc0
    cpnf
    icossicc
    wph
    @15
    cC
    @12
    wcel
    @17
    esummulc2.c
    3ad2ant1
    sseldi
    @14
    @16
    cC
    xrge0adddir
    syl3anc
    @18
    vz
    @19
    @3
    @20
    @1
    @4
    cvv
    @18
    @4
    eqidd
    #
    @18
    @2
    @19
    wceq
    #
    wa
    @2
    @19
    cC
    cxmu
    @18
    @29
    simpr
    oveq1d
    @15
    @17
    @19
    @1
    wcel
    wph
    @14
    @16
    ge0xaddcl
    3adant1
    @18
    @19
    cC
    cxmu
    ovexd
    fvmptd
    @18
    @24
    @21
    @25
    @22
    cxad
    @18
    vz
    @14
    @3
    @21
    @1
    @4
    cvv
    @28
    @18
    @2
    @14
    wceq
    #
    wa
    @2
    @14
    cC
    cxmu
    @18
    @30
    simpr
    oveq1d
    @26
    @18
    @14
    cC
    cxmu
    ovexd
    fvmptd
    @18
    vz
    @16
    @3
    @22
    @1
    @4
    cvv
    @28
    @18
    @2
    @16
    wceq
    #
    wa
    @2
    @16
    cC
    cxmu
    @18
    @31
    simpr
    oveq1d
    @27
    @18
    @16
    cC
    cxmu
    ovexd
    fvmptd
    oveq12d
    3eqtr4d
    esumcocn
    wph
    vz
    @0
    @3
    @6
    @1
    @4
    cvv
    @10
    wph
    @2
    @0
    wceq
    #
    wa
    @2
    @0
    cC
    cxmu
    wph
    @32
    simpr
    oveq1d
    wph
    cA
    cV
    wcel
    cB
    @1
    wcel
    #
    vk
    cA
    wral
    @0
    @1
    wcel
    esummulc2.a
    wph
    @33
    vk
    cA
    esummulc2.b
    ralrimiva
    cA
    cB
    vk
    cV
    vk
    cA
    nfcv
    esumcl
    syl2anc
    wph
    @0
    cC
    cxmu
    ovexd
    fvmptd
    wph
    cA
    @5
    @7
    vk
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    vz
    cB
    @3
    @7
    @1
    @4
    cvv
    @34
    @4
    eqidd
    @34
    @2
    cB
    wceq
    #
    wa
    @2
    cB
    cC
    cxmu
    @34
    @35
    simpr
    oveq1d
    esummulc2.b
    @34
    cB
    cC
    cxmu
    ovexd
    fvmptd
    esumeq2dv
    3eqtr3d
end
