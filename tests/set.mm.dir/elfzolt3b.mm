include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "elfzoel1.mm"
include "elfzoel2.mm"
include "elfzolt3.mm"
include "fzolb.mm"
include "syl3anbrc.mm"

theorem elfzolt3b
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> M e. ( M ..^ N ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    #
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    cM
    cN
    clt
    wbr
    cM
    @0
    wcel
    cK
    cM
    cN
    elfzoel1
    cK
    cM
    cN
    elfzoel2
    cK
    cM
    cN
    elfzolt3
    cM
    cN
    fzolb
    syl3anbrc
end
