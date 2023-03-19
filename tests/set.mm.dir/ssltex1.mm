include "csslt.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wral.mm"
include "w3a.mm"
include "brsslt.mm"
include "simpll.mm"
include "sylbi.mm"

theorem ssltex1
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y


  assert |- ( A <<s B -> A e. _V )

  proof
    cA
    cB
    csslt
    wbr
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    cA
    csur
    wss
    cB
    csur
    wss
    vx
    cv
    vy
    cv
    cslt
    wbr
    vy
    cB
    wral
    vx
    cA
    wral
    w3a
    #
    wa
    @0
    vx
    vy
    cA
    cB
    brsslt
    @0
    @1
    @2
    simpll
    sylbi
end
