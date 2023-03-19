include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cop.mm"
include "eldmg.mm"
include "df-br.mm"
include "exbii.mm"
include "syl6bb.mm"

theorem eldm2g
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x

  disjoint A y
  disjoint B y
  disjoint x y
  disjoint A x
  disjoint B x
  assert |- ( A e. V -> ( A e. dom B <-> E. y <. A , y >. e. B ) )

  proof
    cA
    cV
    wcel
    cA
    cB
    cdm
    wcel
    cA
    vy
    cv
    #
    cB
    wbr
    #
    vy
    wex
    cA
    @0
    cop
    cB
    wcel
    #
    vy
    wex
    vy
    cA
    cB
    cV
    eldmg
    @1
    @2
    vy
    cA
    @0
    cB
    df-br
    exbii
    syl6bb
end
