include "c2.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cz.mm"
include "codd.mm"
include "wceq.mm"
include "breq2.mm"
include "notbid.mm"
include "dfodd3.mm"
include "elrab2.mm"

theorem isodd3
  let cZ: class Z
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x


  assert |- ( Z e. Odd <-> ( Z e. ZZ /\ -. 2 || Z ) )

  proof
    c2
    vz
    cv
    #
    cdvds
    wbr
    #
    wn
    c2
    cZ
    cdvds
    wbr
    #
    wn
    vz
    cZ
    cz
    codd
    @0
    cZ
    wceq
    @1
    @2
    @0
    cZ
    c2
    cdvds
    breq2
    notbid
    vz
    dfodd3
    elrab2
end
