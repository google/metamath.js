include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "elfzoelz.mm"
include "elfzoel2.mm"
include "elfzolt2.mm"
include "fzolb.mm"
include "syl3anbrc.mm"

theorem elfzolt2b
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> K e. ( K ..^ N ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    wcel
    cK
    cz
    wcel
    cN
    cz
    wcel
    cK
    cN
    clt
    wbr
    cK
    cK
    cN
    cfzo
    co
    wcel
    cK
    cM
    cN
    elfzoelz
    cK
    cM
    cN
    elfzoel2
    cK
    cM
    cN
    elfzolt2
    cK
    cN
    fzolb
    syl3anbrc
end
