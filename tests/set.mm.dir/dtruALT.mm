include "cv.mm"
include "wceq.mm"
include "wn.mm"
include "wex.mm"
include "wal.mm"
include "c0.mm"
include "csn.mm"
include "0inp0.mm"
include "p0ex.mm"
include "eqeq2.mm"
include "notbid.mm"
include "spcev.mm"
include "syl.mm"
include "0ex.mm"
include "pm2.61i.mm"
include "exnal.mm"
include "eqcom.mm"
include "albii.mm"
include "xchbinx.mm"
include "mpbi.mm"

theorem dtruALT
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- -. A. x x = y

  proof
    vy
    cv
    #
    vx
    cv
    #
    wceq
    #
    wn
    #
    vx
    wex
    #
    @1
    @0
    wceq
    #
    vx
    wal
    #
    wn
    @0
    c0
    wceq
    #
    @4
    @7
    @0
    c0
    csn
    #
    wceq
    #
    wn
    #
    @4
    @0
    0inp0
    @3
    @10
    vx
    @8
    p0ex
    @1
    @8
    wceq
    @2
    @9
    @1
    @8
    @0
    eqeq2
    notbid
    spcev
    syl
    @3
    @7
    wn
    vx
    c0
    0ex
    @1
    c0
    wceq
    @2
    @7
    @1
    c0
    @0
    eqeq2
    notbid
    spcev
    pm2.61i
    @4
    @2
    vx
    wal
    @6
    @2
    vx
    exnal
    @2
    @5
    vx
    @0
    @1
    eqcom
    albii
    xchbinx
    mpbi
end
