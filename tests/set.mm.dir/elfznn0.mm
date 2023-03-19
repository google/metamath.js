include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "elfz2nn0.mm"
include "simp1bi.mm"

theorem elfznn0
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ... N ) -> K e. NN0 )

  proof
    cK
    cc0
    cN
    cfz
    co
    wcel
    cK
    cn0
    wcel
    cN
    cn0
    wcel
    cK
    cN
    cle
    wbr
    cK
    cN
    elfz2nn0
    simp1bi
end
