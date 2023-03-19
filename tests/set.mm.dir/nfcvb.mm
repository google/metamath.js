include "cv.mm"
include "wnfc.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfnid.mm"
include "eqidd.mm"
include "drnfc1.mm"
include "mtbiri.mm"
include "con2i.mm"
include "nfcvf.mm"
include "impbii.mm"

theorem nfcvb
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/_ x y <-> -. A. x x = y )

  proof
    vx
    vy
    cv
    #
    wnfc
    #
    vx
    vy
    weq
    vx
    wal
    #
    wn
    @2
    @1
    @2
    @1
    vy
    @0
    wnfc
    vy
    nfnid
    vx
    vy
    @0
    @0
    @2
    @0
    eqidd
    drnfc1
    mtbiri
    con2i
    vx
    vy
    nfcvf
    impbii
end
