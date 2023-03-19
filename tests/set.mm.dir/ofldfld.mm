include "cofld.mm"
include "wcel.mm"
include "cfield.mm"
include "corng.mm"
include "isofld.mm"
include "simplbi.mm"

theorem ofldfld
  let cF: class F


  assert |- ( F e. oField -> F e. Field )

  proof
    cF
    cofld
    wcel
    cF
    cfield
    wcel
    cF
    corng
    wcel
    cF
    isofld
    simplbi
end
