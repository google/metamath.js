include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuzb.mm"
include "simplbi.mm"

theorem elfzuz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> K e. ( ZZ>= ` M ) )

  proof
    cK
    cM
    cN
    cfz
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
    elfzuzb
    simplbi
end
