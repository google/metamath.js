include "ccnv.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "df-cnv.mm"
include "eleq2i.mm"
include "elopab.mm"
include "bitri.mm"

theorem elcnv
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  assert |- ( A e. `' R <-> E. x E. y ( A = <. x , y >. /\ y R x ) )

  proof
    cA
    cR
    ccnv
    #
    wcel
    cA
    vy
    cv
    #
    vx
    cv
    #
    cR
    wbr
    #
    vx
    vy
    copab
    #
    wcel
    cA
    @2
    @1
    cop
    wceq
    @3
    wa
    vy
    wex
    vx
    wex
    @0
    @4
    cA
    vx
    vy
    cR
    df-cnv
    eleq2i
    @3
    vx
    vy
    cA
    elopab
    bitri
end
