include "cfld.mm"
include "cdrng.mm"
include "ccm2.mm"
include "cin.mm"
include "df-fld.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"

theorem flddivrng
  let cK: class K


  assert |- ( K e. Fld -> K e. DivRingOps )

  proof
    cfld
    cdrng
    cK
    cfld
    cdrng
    ccm2
    cin
    cdrng
    df-fld
    cdrng
    ccm2
    inss1
    eqsstri
    sseli
end
