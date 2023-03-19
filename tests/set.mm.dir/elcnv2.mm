include "ccnv.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "elcnv.mm"
include "df-br.mm"
include "anbi2i.mm"
include "2exbii.mm"
include "bitri.mm"

theorem elcnv2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R x
  disjoint R y
  assert |- ( A e. `' R <-> E. x E. y ( A = <. x , y >. /\ <. y , x >. e. R ) )

  proof
    cA
    cR
    ccnv
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    #
    @1
    @0
    cR
    wbr
    #
    wa
    #
    vy
    wex
    vx
    wex
    @2
    @1
    @0
    cop
    cR
    wcel
    #
    wa
    #
    vy
    wex
    vx
    wex
    vx
    vy
    cA
    cR
    elcnv
    @4
    @6
    vx
    vy
    @3
    @5
    @2
    @1
    @0
    cR
    df-br
    anbi2i
    2exbii
    bitri
end
