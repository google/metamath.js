include "wcel.mm"
include "wf1o.mm"
include "w3a.mm"
include "cvv.mm"
include "cen.mm"
include "wbr.mm"
include "wf.mm"
include "f1of.mm"
include "fex2.mm"
include "syl3an1.mm"
include "3coml.mm"
include "simp3.mm"
include "f1oen3g.mm"
include "syl2anc.mm"

theorem f1oen2g
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let vf: setvar f


  assert |- ( ( A e. V /\ B e. W /\ F : A -1-1-onto-> B ) -> A ~~ B )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cA
    cB
    cF
    wf1o
    #
    w3a
    cF
    cvv
    wcel
    #
    @2
    cA
    cB
    cen
    wbr
    @2
    @0
    @1
    @3
    @2
    cA
    cB
    cF
    wf
    @0
    @1
    @3
    cA
    cB
    cF
    f1of
    cA
    cB
    cF
    cV
    cW
    fex2
    syl3an1
    3coml
    @0
    @1
    @2
    simp3
    cA
    cB
    cF
    cvv
    f1oen3g
    syl2anc
end
