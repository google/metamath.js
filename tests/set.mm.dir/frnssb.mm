include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "wfn.mm"
include "simpr.mm"
include "ffn.mm"
include "anim12ci.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "simpl.mm"
include "anim1i.mm"
include "ancomd.mm"
include "fss.mm"
include "syl.mm"
include "impbida.mm"

theorem frnssb
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W

  disjoint A k
  disjoint F k
  disjoint V k
  assert |- ( ( V C_ W /\ A. k e. A ( F ` k ) e. V ) -> ( F : A --> W <-> F : A --> V ) )

  proof
    cV
    cW
    wss
    #
    vk
    cv
    cF
    cfv
    cV
    wcel
    vk
    cA
    wral
    #
    wa
    #
    cA
    cW
    cF
    wf
    #
    cA
    cV
    cF
    wf
    #
    @2
    @3
    wa
    cF
    cA
    wfn
    #
    @1
    wa
    @4
    @2
    @1
    @3
    @5
    @0
    @1
    simpr
    cA
    cW
    cF
    ffn
    anim12ci
    vk
    cA
    cV
    cF
    ffnfv
    sylibr
    @2
    @4
    wa
    #
    @4
    @0
    wa
    @3
    @6
    @0
    @4
    @2
    @0
    @4
    @0
    @1
    simpl
    anim1i
    ancomd
    cA
    cV
    cW
    cF
    fss
    syl
    impbida
end
