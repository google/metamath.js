include "cdmn.mm"
include "wcel.mm"
include "cprrng.mm"
include "ccring.mm"
include "isdmn2.mm"
include "simprbi.mm"

theorem dmncrng
  let cR: class R


  assert |- ( R e. Dmn -> R e. CRingOps )

  proof
    cR
    cdmn
    wcel
    cR
    cprrng
    wcel
    cR
    ccring
    wcel
    cR
    isdmn2
    simprbi
end
