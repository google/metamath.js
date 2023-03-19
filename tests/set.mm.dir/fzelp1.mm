include "cfz.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "fzssp1.mm"
include "sseli.mm"

theorem fzelp1
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> K e. ( M ... ( N + 1 ) ) )

  proof
    cM
    cN
    cfz
    co
    cM
    cN
    c1
    caddc
    co
    cfz
    co
    cK
    cM
    cN
    fzssp1
    sseli
end
