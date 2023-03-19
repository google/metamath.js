include "cz.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "eluz1.mm"
include "baibd.mm"

theorem eluz
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( N e. ( ZZ>= ` M ) <-> M <_ N ) )

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
    cM
    cN
    eluz1
    baibd
end
