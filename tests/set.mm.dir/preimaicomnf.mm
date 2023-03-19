include "ccnv.mm"
include "cmnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "clt.mm"
include "wbr.mm"
include "wfn.mm"
include "wceq.mm"
include "cxr.mm"
include "ffnd.mm"
include "fncnvima2.mm"
include "syl.mm"
include "wa.mm"
include "mnfxr.mm"
include "a1i.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "icoltub.mm"
include "syl3anc.mm"
include "ex.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "cle.mm"
include "mnfled.mm"
include "elicod.mm"
include "impbid.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem preimaicomnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  assume preimaicomnf.1: |- ( ph -> F : A --> RR* )
  assume preimaicomnf.2: |- ( ph -> B e. RR* )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( `' F " ( -oo [,) B ) ) = { x e. A | ( F ` x ) < B } )

  proof
    wph
    cF
    ccnv
    cmnf
    cB
    cico
    co
    #
    cima
    #
    vx
    cv
    #
    cF
    cfv
    #
    @0
    wcel
    #
    vx
    cA
    crab
    #
    @3
    cB
    clt
    wbr
    #
    vx
    cA
    crab
    wph
    cF
    cA
    wfn
    @1
    @5
    wceq
    wph
    cA
    cxr
    cF
    preimaicomnf.1
    ffnd
    vx
    cA
    @0
    cF
    fncnvima2
    syl
    wph
    @4
    @6
    vx
    cA
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @4
    @6
    @8
    @4
    @6
    @8
    @4
    wa
    #
    cmnf
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @4
    @6
    @10
    @9
    mnfxr
    a1i
    wph
    @11
    @7
    @4
    preimaicomnf.2
    ad2antrr
    @8
    @4
    simpr
    cmnf
    cB
    @3
    icoltub
    syl3anc
    ex
    @8
    @6
    @4
    @8
    @6
    wa
    #
    cmnf
    cB
    @3
    @10
    @12
    mnfxr
    a1i
    wph
    @11
    @7
    @6
    preimaicomnf.2
    ad2antrr
    @8
    @3
    cxr
    wcel
    @6
    wph
    cA
    cxr
    @2
    cF
    preimaicomnf.1
    ffvelrnda
    #
    adantr
    @8
    cmnf
    @3
    cle
    wbr
    @6
    @8
    @3
    @13
    mnfled
    adantr
    @8
    @6
    simpr
    elicod
    ex
    impbid
    rabbidva
    eqtrd
end
