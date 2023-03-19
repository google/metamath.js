include "ccnv.mm"
include "wceq.mm"
include "crels.mm"
include "wcel.mm"
include "wss.mm"
include "eqcom.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "elrelscnveq3.mm"
include "cnvsym.mm"
include "syl6bbr.mm"
include "syl5rbbr.mm"

theorem elrelscnveq
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. Rels -> ( `' R C_ R <-> `' R = R ) )

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
    crels
    wcel
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
    elrelscnveq3
    vx
    vy
    cR
    cnvsym
    syl6bbr
    syl5rbbr
end
