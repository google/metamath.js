include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "elfzoel1.mm"
include "zred.mm"
include "elfzoelz.mm"
include "elfzoel2.mm"
include "elfzole1.mm"
include "elfzolt2.mm"
include "lelttrd.mm"

theorem elfzolt3
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> M < N )

  proof
    cK
    cM
    cN
    cfzo
    co
    wcel
    #
    cM
    cK
    cN
    @0
    cM
    cK
    cM
    cN
    elfzoel1
    zred
    @0
    cK
    cK
    cM
    cN
    elfzoelz
    zred
    @0
    cN
    cK
    cM
    cN
    elfzoel2
    zred
    cK
    cM
    cN
    elfzole1
    cK
    cM
    cN
    elfzolt2
    lelttrd
end
