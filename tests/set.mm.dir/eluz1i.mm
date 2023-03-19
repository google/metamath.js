include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "eluz1.mm"
include "ax-mp.mm"

theorem eluz1i
  let cM: class M
  let cN: class N
  assume eluz.1: |- M e. ZZ


  assert |- ( N e. ( ZZ>= ` M ) <-> ( N e. ZZ /\ M <_ N ) )

  proof
    cM
    cz
    wcel
    cN
    cM
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    cM
    cN
    cle
    wbr
    wa
    wb
    eluz.1
    cM
    cN
    eluz1
    ax-mp
end
