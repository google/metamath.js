include "cesum.mm"
include "c1.mm"
include "cxdiv.mm"
include "co.mm"
include "cxmu.mm"
include "cdiv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cr.mm"
include "wcel.mm"
include "wne.mm"
include "wceq.mm"
include "1red.mm"
include "rpred.mm"
include "rpne0d.mm"
include "rexdiv.mm"
include "syl3anc.mm"
include "crp.mm"
include "cioo.mm"
include "ioorp.mm"
include "ioossico.mm"
include "eqsstr3i.mm"
include "rpreccld.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "esummulc1.mm"
include "cxr.mm"
include "cicc.mm"
include "iccssxr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "xdivrec.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "esumeq2dv.mm"
include "3eqtr4d.mm"

theorem esumdivc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume esumdivc.a: |- ( ph -> A e. V )
  assume esumdivc.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume esumdivc.c: |- ( ph -> C e. RR+ )

  disjoint A k
  disjoint C k
  disjoint V k
  disjoint k ph
  assert |- ( ph -> ( sum* k e. A B /e C ) = sum* k e. A ( B /e C ) )

  proof
    wph
    cA
    cB
    vk
    cesum
    #
    c1
    cC
    cxdiv
    co
    #
    cxmu
    co
    #
    cA
    cB
    @1
    cxmu
    co
    #
    vk
    cesum
    @0
    cC
    cxdiv
    co
    #
    cA
    cB
    cC
    cxdiv
    co
    #
    vk
    cesum
    wph
    cA
    cB
    @1
    vk
    cV
    esumdivc.a
    esumdivc.b
    wph
    @1
    c1
    cC
    cdiv
    co
    #
    cc0
    cpnf
    cico
    co
    #
    wph
    c1
    cr
    wcel
    cC
    cr
    wcel
    #
    cC
    cc0
    wne
    #
    @1
    @6
    wceq
    wph
    1red
    wph
    cC
    esumdivc.c
    rpred
    #
    wph
    cC
    esumdivc.c
    rpne0d
    #
    c1
    cC
    rexdiv
    syl3anc
    wph
    crp
    @7
    @6
    crp
    cc0
    cpnf
    cioo
    co
    @7
    ioorp
    cc0
    cpnf
    ioossico
    eqsstr3i
    wph
    cC
    esumdivc.c
    rpreccld
    sseldi
    eqeltrd
    esummulc1
    wph
    @0
    cxr
    wcel
    @8
    @9
    @4
    @2
    wceq
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
    @12
    wcel
    #
    vk
    cA
    wral
    @0
    @12
    wcel
    esumdivc.a
    wph
    @14
    vk
    cA
    esumdivc.b
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
    @10
    @11
    @0
    cC
    xdivrec
    syl3anc
    wph
    cA
    @5
    @3
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
    @8
    @9
    @5
    @3
    wceq
    @16
    @12
    cxr
    cB
    @13
    esumdivc.b
    sseldi
    wph
    @8
    @15
    @10
    adantr
    wph
    @9
    @15
    @11
    adantr
    cB
    cC
    xdivrec
    syl3anc
    esumeq2dv
    3eqtr4d
end
