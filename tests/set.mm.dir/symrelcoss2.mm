include "ccoss.mm"
include "ccnv.mm"
include "wss.mm"
include "wrel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "symrelcoss3.mm"
include "cnvsym.mm"
include "anbi1i.mm"
include "mpbir.mm"

theorem symrelcoss2
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( `' ,~ R C_ ,~ R /\ Rel ,~ R )

  proof
    cR
    ccoss
    #
    ccnv
    @0
    wss
    #
    @0
    wrel
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    @4
    @3
    @0
    wbr
    wi
    vy
    wal
    vx
    wal
    #
    @2
    wa
    vx
    vy
    cR
    symrelcoss3
    @1
    @5
    @2
    vx
    vy
    @0
    cnvsym
    anbi1i
    mpbir
end
