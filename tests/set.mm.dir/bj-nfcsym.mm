include "weq.mm"
include "wal.mm"
include "cv.mm"
include "wnfc.mm"
include "wb.mm"
include "sp.mm"
include "equcomd.mm"
include "drnfc1.mm"
include "wn.mm"
include "nfcvf.mm"
include "nfcvf2.mm"
include "2thd.mm"
include "pm2.61i.mm"

theorem bj-nfcsym
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/_ x y <-> F/_ y x )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vy
    cv
    #
    wnfc
    #
    vy
    vx
    cv
    #
    wnfc
    #
    wb
    vx
    vy
    @2
    @4
    @1
    vx
    vy
    @0
    vx
    sp
    equcomd
    drnfc1
    @1
    wn
    @3
    @5
    vx
    vy
    nfcvf
    vx
    vy
    nfcvf2
    2thd
    pm2.61i
end
