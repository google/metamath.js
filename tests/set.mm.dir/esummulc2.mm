include "cesum.mm"
include "cxmu.mm"
include "co.mm"
include "cxr.mm"
include "wcel.mm"
include "wceq.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "icossxr.mm"
include "sseldi.mm"
include "cicc.mm"
include "iccssxr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "xmulcom.mm"
include "esummulc1.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "esumeq2dv.mm"
include "3eqtrd.mm"

theorem esummulc2
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
  assert |- ( ph -> ( C *e sum* k e. A B ) = sum* k e. A ( C *e B ) )

  proof
    wph
    cC
    cA
    cB
    vk
    cesum
    #
    cxmu
    co
    #
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
    cA
    cC
    cB
    cxmu
    co
    #
    vk
    cesum
    wph
    cC
    cxr
    wcel
    #
    @0
    cxr
    wcel
    @1
    @2
    wceq
    wph
    cc0
    cpnf
    cico
    co
    cxr
    cC
    cc0
    cpnf
    icossxr
    esummulc2.c
    sseldi
    #
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @0
    cc0
    cpnf
    iccssxr
    #
    wph
    cA
    cV
    wcel
    cB
    @7
    wcel
    #
    vk
    cA
    wral
    @0
    @7
    wcel
    esummulc2.a
    wph
    @9
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
    sseldi
    cC
    @0
    xmulcom
    syl2anc
    wph
    cA
    cB
    cC
    vk
    cV
    esummulc2.a
    esummulc2.b
    esummulc2.c
    esummulc1
    wph
    cA
    @3
    @4
    vk
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    #
    cB
    cxr
    wcel
    @5
    @3
    @4
    wceq
    @11
    @7
    cxr
    cB
    @8
    esummulc2.b
    sseldi
    wph
    @5
    @10
    @6
    adantr
    cB
    cC
    xmulcom
    syl2anc
    esumeq2dv
    3eqtrd
end
