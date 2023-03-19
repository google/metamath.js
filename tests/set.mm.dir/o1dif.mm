include "cmpt.mm"
include "co1.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cof.mm"
include "wi.mm"
include "o1sub.mm"
include "expcom.mm"
include "syl.mm"
include "cvv.mm"
include "cc.mm"
include "cr.mm"
include "wss.mm"
include "cdm.mm"
include "wral.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "subcld.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "o1dm.mm"
include "eqsstr3d.mm"
include "reex.mm"
include "ssex.mm"
include "eqidd.mm"
include "offval2.mm"
include "nncand.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "caddc.mm"
include "o1add.mm"
include "ex.mm"
include "npcand.mm"
include "impbid.mm"

theorem o1dif
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume o1dif.1: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume o1dif.2: |- ( ( ph /\ x e. A ) -> C e. CC )
  assume o1dif.3: |- ( ph -> ( x e. A |-> ( B - C ) ) e. O(1) )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> ( ( x e. A |-> B ) e. O(1) <-> ( x e. A |-> C ) e. O(1) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    co1
    wcel
    #
    vx
    cA
    cC
    cmpt
    #
    co1
    wcel
    #
    wph
    @1
    @0
    vx
    cA
    cB
    cC
    cmin
    co
    #
    cmpt
    #
    cmin
    cof
    co
    #
    co1
    wcel
    #
    @3
    wph
    @5
    co1
    wcel
    #
    @1
    @7
    wi
    o1dif.3
    @1
    @8
    @7
    @0
    @5
    o1sub
    expcom
    syl
    wph
    @6
    @2
    co1
    wph
    @6
    vx
    cA
    cB
    @4
    cmin
    co
    #
    cmpt
    @2
    wph
    vx
    cA
    cB
    @4
    cmin
    @0
    @5
    cvv
    cc
    cc
    wph
    cA
    cr
    wss
    cA
    cvv
    wcel
    wph
    cA
    @5
    cdm
    #
    cr
    wph
    @4
    cc
    wcel
    #
    vx
    cA
    wral
    @10
    cA
    wceq
    wph
    @11
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    cB
    cC
    o1dif.1
    o1dif.2
    subcld
    #
    ralrimiva
    vx
    cA
    @4
    cc
    dmmptg
    syl
    wph
    @8
    @10
    cr
    wss
    o1dif.3
    @5
    o1dm
    syl
    eqsstr3d
    cA
    cr
    reex
    ssex
    syl
    #
    o1dif.1
    @13
    wph
    @0
    eqidd
    wph
    @5
    eqidd
    #
    offval2
    wph
    vx
    cA
    @9
    cC
    @12
    cB
    cC
    o1dif.1
    o1dif.2
    nncand
    mpteq2dva
    eqtrd
    eleq1d
    sylibd
    wph
    @3
    @5
    @2
    caddc
    cof
    co
    #
    co1
    wcel
    #
    @1
    wph
    @8
    @3
    @17
    wi
    o1dif.3
    @8
    @3
    @17
    @5
    @2
    o1add
    ex
    syl
    wph
    @16
    @0
    co1
    wph
    @16
    vx
    cA
    @4
    cC
    caddc
    co
    #
    cmpt
    @0
    wph
    vx
    cA
    @4
    cC
    caddc
    @5
    @2
    cvv
    cc
    cc
    @14
    @13
    o1dif.2
    @15
    wph
    @2
    eqidd
    offval2
    wph
    vx
    cA
    @18
    cB
    @12
    cB
    cC
    o1dif.1
    o1dif.2
    npcand
    mpteq2dva
    eqtrd
    eleq1d
    sylibd
    impbid
end
