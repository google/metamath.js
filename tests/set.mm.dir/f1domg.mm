include "wcel.mm"
include "wf1.mm"
include "cv.mm"
include "wex.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "f1dmex.mm"
include "wf.mm"
include "f1f.mm"
include "fex.mm"
include "sylan.mm"
include "syldan.mm"
include "expcom.mm"
include "f1eq1.mm"
include "spcegv.mm"
include "syli.mm"
include "brdomg.mm"
include "sylibrd.mm"

theorem f1domg
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vf: setvar f


  assert |- ( B e. C -> ( F : A -1-1-> B -> A ~<_ B ) )

  proof
    cB
    cC
    wcel
    #
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    cA
    cB
    cdom
    wbr
    @1
    @0
    cF
    cvv
    wcel
    #
    @4
    @1
    @0
    @5
    @1
    @0
    cA
    cvv
    wcel
    #
    @5
    cA
    cB
    cC
    cF
    f1dmex
    @1
    cA
    cB
    cF
    wf
    @6
    @5
    cA
    cB
    cF
    f1f
    cA
    cB
    cvv
    cF
    fex
    sylan
    syldan
    expcom
    @3
    @1
    vf
    cF
    cvv
    cA
    cB
    @2
    cF
    f1eq1
    spcegv
    syli
    cA
    cB
    cC
    vf
    brdomg
    sylibrd
end
