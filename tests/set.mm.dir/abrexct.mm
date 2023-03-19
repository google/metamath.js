include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "1stcrestlem.mm"
include "syl5eqbrr.mm"

theorem abrexct
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- ( A ~<_ _om -> { y | E. x e. A y = B } ~<_ _om )

  proof
    cA
    com
    cdom
    wbr
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    vx
    cA
    cB
    cmpt
    #
    crn
    com
    cdom
    vx
    vy
    cA
    cB
    @0
    @0
    eqid
    rnmpt
    vx
    cA
    cB
    1stcrestlem
    syl5eqbrr
end
