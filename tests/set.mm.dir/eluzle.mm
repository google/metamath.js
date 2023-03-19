include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "eluz2.mm"
include "simp3bi.mm"

theorem eluzle
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> M <_ N )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    cM
    cz
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
    eluz2
    simp3bi
end
