include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "eluzelre.mm"
include "recnd.mm"

theorem eluzelcn
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> N e. CC )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    cN
    cM
    cN
    eluzelre
    recnd
end
