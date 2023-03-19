include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzuzb.mm"
include "simprbi.mm"

theorem elfzuz3
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) -> N e. ( ZZ>= ` K ) )

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
    simprbi
end
