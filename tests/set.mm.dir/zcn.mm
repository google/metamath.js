include "cz.mm"
include "wcel.mm"
include "zre.mm"
include "recnd.mm"

theorem zcn
  let cN: class N


  assert |- ( N e. ZZ -> N e. CC )

  proof
    cN
    cz
    wcel
    cN
    cN
    zre
    recnd
end
