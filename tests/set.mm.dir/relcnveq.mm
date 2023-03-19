include "ccnv.mm"
include "wceq.mm"
include "wrel.mm"
include "wss.mm"
include "eqcom.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "relcnveq3.mm"
include "cnvsym.mm"
include "syl6bbr.mm"
include "syl5rbbr.mm"

theorem relcnveq
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( Rel R -> ( `' R C_ R <-> `' R = R ) )

  proof
    cR
    ccnv
    #
    cR
    wceq
    cR
    @0
    wceq
    #
    cR
    wrel
    #
    @0
    cR
    wss
    #
    cR
    @0
    eqcom
    @2
    @1
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    @5
    @4
    cR
    wbr
    wi
    vy
    wal
    vx
    wal
    @3
    vx
    vy
    cR
    relcnveq3
    vx
    vy
    cR
    cnvsym
    syl6bbr
    syl5rbbr
end
