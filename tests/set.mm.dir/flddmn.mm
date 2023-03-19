include "cdrng.mm"
include "wcel.mm"
include "ccring.mm"
include "wa.mm"
include "cprrng.mm"
include "cfld.mm"
include "cdmn.mm"
include "divrngpr.mm"
include "anim1i.mm"
include "isfld2.mm"
include "isdmn2.mm"
include "3imtr4i.mm"

theorem flddmn
  let cK: class K


  assert |- ( K e. Fld -> K e. Dmn )

  proof
    cK
    cdrng
    wcel
    #
    cK
    ccring
    wcel
    #
    wa
    cK
    cprrng
    wcel
    #
    @1
    wa
    cK
    cfld
    wcel
    cK
    cdmn
    wcel
    @0
    @2
    @1
    cK
    divrngpr
    anim1i
    cK
    isfld2
    cK
    isdmn2
    3imtr4i
end
