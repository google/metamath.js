include "wrel.mm"
include "ccnv.mm"
include "wbr.mm"
include "wb.mm"
include "relbrcnvg.mm"
include "ax-mp.mm"

theorem relbrcnv
  let cA: class A
  let cB: class B
  let cR: class R
  assume relbrcnv.1: |- Rel R


  assert |- ( A `' R B <-> B R A )

  proof
    cR
    wrel
    cA
    cB
    cR
    ccnv
    wbr
    cB
    cA
    cR
    wbr
    wb
    relbrcnv.1
    cA
    cB
    cR
    relbrcnvg
    ax-mp
end
