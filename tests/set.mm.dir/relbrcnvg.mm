include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "wbr.mm"
include "wi.mm"
include "relcnv.mm"
include "brrelex12.mm"
include "mpan.mm"
include "a1i.mm"
include "ancomd.mm"
include "ex.mm"
include "wb.mm"
include "brcnvg.mm"
include "pm5.21ndd.mm"

theorem relbrcnvg
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( Rel R -> ( A `' R B <-> B R A ) )

  proof
    cR
    wrel
    #
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cA
    cB
    cR
    ccnv
    #
    wbr
    #
    cB
    cA
    cR
    wbr
    #
    @5
    @3
    wi
    @0
    @4
    wrel
    @5
    @3
    cR
    relcnv
    cA
    cB
    @4
    brrelex12
    mpan
    a1i
    @0
    @6
    @3
    @0
    @6
    wa
    @2
    @1
    cB
    cA
    cR
    brrelex12
    ancomd
    ex
    @3
    @5
    @6
    wb
    wi
    @0
    cA
    cB
    cvv
    cvv
    cR
    brcnvg
    a1i
    pm5.21ndd
end
