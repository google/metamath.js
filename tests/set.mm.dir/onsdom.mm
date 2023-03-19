include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "char.mm"
include "cfv.mm"
include "con0.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "harcl.mm"
include "harsdom.mm"
include "breq2.mm"
include "rspcev.mm"
include "sylancr.mm"

theorem onsdom
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. dom card -> E. x e. On A ~< x )

  proof
    cA
    ccrd
    cdm
    wcel
    cA
    char
    cfv
    #
    con0
    wcel
    cA
    @0
    csdm
    wbr
    #
    cA
    vx
    cv
    #
    csdm
    wbr
    #
    vx
    con0
    wrex
    cA
    harcl
    cA
    harsdom
    @3
    @1
    vx
    @0
    con0
    @2
    @0
    cA
    csdm
    breq2
    rspcev
    sylancr
end
