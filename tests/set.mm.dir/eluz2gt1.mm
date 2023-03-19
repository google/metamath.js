include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "eluz2b1.mm"
include "simprbi.mm"

theorem eluz2gt1
  let cN: class N


  assert |- ( N e. ( ZZ>= ` 2 ) -> 1 < N )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    c1
    cN
    clt
    wbr
    cN
    eluz2b1
    simprbi
end
