include "wcel.mm"
include "wf1o.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "cen.mm"
include "wbr.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "imp.mm"
include "bren.mm"
include "sylibr.mm"

theorem f1oen3g
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vf: setvar f


  assert |- ( ( F e. V /\ F : A -1-1-onto-> B ) -> A ~~ B )

  proof
    cF
    cV
    wcel
    #
    cA
    cB
    cF
    wf1o
    #
    wa
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cA
    cB
    cen
    wbr
    @0
    @1
    @4
    @3
    @1
    vf
    cF
    cV
    cA
    cB
    @2
    cF
    f1oeq1
    spcegv
    imp
    cA
    cB
    vf
    bren
    sylibr
end
