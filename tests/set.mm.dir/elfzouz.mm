include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo2.mm"
include "simp1bi.mm"

theorem elfzouz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) -> K e. ( ZZ>= ` M ) )

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
    cz
    wcel
    cK
    cN
    clt
    wbr
    cK
    cM
    cN
    elfzo2
    simp1bi
end
