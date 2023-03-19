include "c2.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "ceven.mm"
include "breq2.mm"
include "dfeven2.mm"
include "elrab2.mm"

theorem iseven2
  let cZ: class Z
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Even <-> ( Z e. ZZ /\ 2 || Z ) )

  proof
    c2
    vz
    cv
    #
    cdvds
    wbr
    c2
    cZ
    cdvds
    wbr
    vz
    cZ
    cz
    ceven
    @0
    cZ
    c2
    cdvds
    breq2
    vz
    dfeven2
    elrab2
end
