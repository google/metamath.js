include "wcel.mm"
include "crn.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "wbr.mm"
include "elrn2g.mm"
include "df-br.mm"
include "exbii.mm"
include "syl6bbr.mm"

theorem elrng
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( A e. V -> ( A e. ran B <-> E. x x B A ) )

  proof
    cA
    cV
    wcel
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
    cV
    elrn2g
    @2
    @1
    vx
    @0
    cA
    cB
    df-br
    exbii
    syl6bbr
end
