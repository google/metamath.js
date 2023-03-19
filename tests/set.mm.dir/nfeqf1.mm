include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wnf.mm"
include "nfeqf2.mm"
include "equcom.mm"
include "nfbii.mm"
include "sylib.mm"

theorem nfeqf1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> F/ x y = z )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    vz
    vy
    weq
    #
    vx
    wnf
    vy
    vz
    weq
    #
    vx
    wnf
    vx
    vy
    vz
    nfeqf2
    @0
    @1
    vx
    vz
    vy
    equcom
    nfbii
    sylib
end
