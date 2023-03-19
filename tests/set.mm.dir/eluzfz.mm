include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "elfzuzb.mm"
include "biimpri.mm"

theorem eluzfz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ( ZZ>= ` M ) /\ N e. ( ZZ>= ` K ) ) -> K e. ( M ... N ) )

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
    wa
    cK
    cM
    cN
    elfzuzb
    biimpri
end
