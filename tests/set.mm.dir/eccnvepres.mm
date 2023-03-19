include "wcel.mm"
include "cv.mm"
include "cep.mm"
include "ccnv.mm"
include "wbr.mm"
include "wa.mm"
include "cab.mm"
include "cres.mm"
include "cec.mm"
include "crab.mm"
include "brcnvep.mm"
include "anbi1cd.mm"
include "abbidv.mm"
include "ecres.mm"
include "df-rab.mm"
include "3eqtr4g.mm"

theorem eccnvepres
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  disjoint B x
  disjoint V x
  assert |- ( B e. V -> [ B ] ( `' _E |` A ) = { x e. B | B e. A } )

  proof
    cB
    cV
    wcel
    #
    cB
    cA
    wcel
    #
    cB
    vx
    cv
    #
    cep
    ccnv
    #
    wbr
    #
    wa
    #
    vx
    cab
    @2
    cB
    wcel
    #
    @1
    wa
    #
    vx
    cab
    cB
    @3
    cA
    cres
    cec
    @1
    vx
    cB
    crab
    @0
    @5
    @7
    vx
    @0
    @4
    @6
    @1
    cB
    @2
    cV
    brcnvep
    anbi1cd
    abbidv
    vx
    cA
    cB
    @3
    ecres
    @1
    vx
    cB
    df-rab
    3eqtr4g
end
