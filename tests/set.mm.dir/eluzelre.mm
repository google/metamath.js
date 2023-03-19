include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "eluzelz.mm"
include "zred.mm"

theorem eluzelre
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> N e. RR )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    cN
    cM
    cN
    eluzelz
    zred
end
