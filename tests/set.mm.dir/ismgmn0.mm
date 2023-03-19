include "wcel.mm"
include "cvv.mm"
include "cmgm.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wb.mm"
include "cbs.mm"
include "cfv.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "elfvexd.mm"
include "ismgm.mm"
include "syl.mm"

theorem ismgmn0
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cM: class M
  let c.op: class .o.
  assume ismgmn0.b: |- B = ( Base ` M )
  assume ismgmn0.o: |- .o. = ( +g ` M )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint .o. x
  disjoint .o. y
  assert |- ( A e. B -> ( M e. Mgm <-> A. x e. B A. y e. B ( x .o. y ) e. B ) )

  proof
    cA
    cB
    wcel
    #
    cM
    cvv
    wcel
    cM
    cmgm
    wcel
    vx
    cv
    vy
    cv
    c.op
    co
    cB
    wcel
    vy
    cB
    wral
    vx
    cB
    wral
    wb
    @0
    cA
    cbs
    cM
    @0
    cA
    cM
    cbs
    cfv
    #
    wcel
    cB
    @1
    cA
    ismgmn0.b
    eleq2i
    biimpi
    elfvexd
    vx
    vy
    cB
    cM
    cvv
    c.op
    ismgmn0.b
    ismgmn0.o
    ismgm
    syl
end
