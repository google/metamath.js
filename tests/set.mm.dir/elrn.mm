include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "wbr.mm"
include "elrn2.mm"
include "df-br.mm"
include "exbii.mm"
include "bitr4i.mm"

theorem elrn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume elrn.1: |- A e. _V

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A e. ran B <-> E. x x B A )

  proof
    cA
    cB
    crn
    wcel
    vx
    cv
    #
    cA
    cop
    cB
    wcel
    #
    vx
    wex
    @0
    cA
    cB
    wbr
    #
    vx
    wex
    vx
    cA
    cB
    elrn.1
    elrn2
    @2
    @1
    vx
    @0
    cA
    cB
    df-br
    exbii
    bitr4i
end
