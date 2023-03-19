include "cmpt.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "co1.mm"
include "cvv.mm"
include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "cdm.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "o1dm.mm"
include "eqsstr3d.mm"
include "reex.mm"
include "ssex.mm"
include "eqidd.mm"
include "offval2.mm"
include "o1sub.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem o1sub2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vc: setvar c
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume o1add2.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume o1add2.2: |- ( ( ph /\ x e. A ) -> C e. V )
  assume o1add2.3: |- ( ph -> ( x e. A |-> B ) e. O(1) )
  assume o1add2.4: |- ( ph -> ( x e. A |-> C ) e. O(1) )

  disjoint A x
  disjoint ph x
  disjoint c m
  disjoint c n
  disjoint c p
  disjoint c x
  disjoint A c
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint B c
  disjoint B m
  disjoint B n
  disjoint B p
  disjoint C c
  disjoint C m
  disjoint C n
  disjoint C p
  disjoint c ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
  assert |- ( ph -> ( x e. A |-> ( B - C ) ) e. O(1) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    vx
    cA
    cC
    cmpt
    #
    cmin
    cof
    co
    #
    vx
    cA
    cB
    cC
    cmin
    co
    cmpt
    co1
    wph
    vx
    cA
    cB
    cC
    cmin
    @0
    @1
    cvv
    cV
    cV
    wph
    cA
    cr
    wss
    cA
    cvv
    wcel
    wph
    cA
    @0
    cdm
    #
    cr
    wph
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    @3
    cA
    wceq
    wph
    @4
    vx
    cA
    o1add2.1
    ralrimiva
    vx
    cA
    cB
    cV
    dmmptg
    syl
    wph
    @0
    co1
    wcel
    #
    @3
    cr
    wss
    o1add2.3
    @0
    o1dm
    syl
    eqsstr3d
    cA
    cr
    reex
    ssex
    syl
    o1add2.1
    o1add2.2
    wph
    @0
    eqidd
    wph
    @1
    eqidd
    offval2
    wph
    @5
    @1
    co1
    wcel
    @2
    co1
    wcel
    o1add2.3
    o1add2.4
    @0
    @1
    o1sub
    syl2anc
    eqeltrrd
end
