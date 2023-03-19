include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "eluz2.mm"
include "simp2bi.mm"

theorem eluzelz
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> N e. ZZ )

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
    simp2bi
end
