include "cv.mm"
include "wrel.mm"
include "wrex.mm"
include "ciin.mm"
include "cint.mm"
include "reliin.mm"
include "intiin.mm"
include "releqi.mm"
include "sylibr.mm"

theorem relint
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( E. x e. A Rel x -> Rel |^| A )

  proof
    vx
    cv
    #
    wrel
    vx
    cA
    wrex
    vx
    cA
    @0
    ciin
    #
    wrel
    cA
    cint
    #
    wrel
    vx
    cA
    @0
    reliin
    @2
    @1
    vx
    cA
    intiin
    releqi
    sylibr
end
