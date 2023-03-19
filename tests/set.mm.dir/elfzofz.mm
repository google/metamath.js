include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cfz.mm"
include "elfzouz.mm"
include "elfzouz2.mm"
include "elfzuzb.mm"
include "sylanbrc.mm"

theorem elfzofz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> K e. ( M ... N ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    wcel
    cK
    cM
    cuz
    cfv
    wcel
    cN
    cK
    cuz
    cfv
    wcel
    cK
    cM
    cN
    cfz
    co
    wcel
    cK
    cM
    cN
    elfzouz
    cK
    cM
    cN
    elfzouz2
    cK
    cM
    cN
    elfzuzb
    sylanbrc
end
