include "ccoss.mm"
include "ccnv.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "cvv.mm"
include "brcosscnvcoss.mm"
include "el2v.mm"
include "biimpi.mm"
include "gen2.mm"
include "cnvsym.mm"
include "mpbir.mm"
include "wrel.mm"
include "relcoss.mm"
include "relcnveq.mm"
include "ax-mp.mm"
include "mpbi.mm"

theorem cnvcosseq
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- `' ,~ R = ,~ R

  proof
    cR
    ccoss
    #
    ccnv
    #
    @0
    wss
    #
    @1
    @0
    wceq
    #
    @2
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    @5
    @4
    @0
    wbr
    #
    wi
    #
    vy
    wal
    vx
    wal
    @8
    vx
    vy
    @6
    @7
    @6
    @7
    wb
    vx
    vy
    @4
    @5
    cR
    cvv
    cvv
    brcosscnvcoss
    el2v
    biimpi
    gen2
    vx
    vy
    @0
    cnvsym
    mpbir
    @0
    wrel
    @2
    @3
    wb
    cR
    relcoss
    @0
    relcnveq
    ax-mp
    mpbi
end
