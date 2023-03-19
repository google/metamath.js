include "ccnv.mm"
include "cec.mm"
include "wcel.mm"
include "wbr.mm"
include "wrel.mm"
include "wb.mm"
include "relcnv.mm"
include "relelec.mm"
include "ax-mp.mm"
include "relbrcnvg.mm"
include "syl5bb.mm"

theorem releleccnv
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( Rel R -> ( A e. [ B ] `' R <-> A R B ) )

  proof
    cA
    cB
    cR
    ccnv
    #
    cec
    wcel
    #
    cB
    cA
    @0
    wbr
    #
    cR
    wrel
    cA
    cB
    cR
    wbr
    @0
    wrel
    @1
    @2
    wb
    cR
    relcnv
    cA
    cB
    @0
    relelec
    ax-mp
    cB
    cA
    cR
    relbrcnvg
    syl5bb
end
