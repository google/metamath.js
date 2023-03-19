include "wel.mm"
include "wn.mm"
include "wal.mm"
include "cio.mm"
include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "weu.mm"
include "wb.mm"
include "0ex.mm"
include "eueq1.mm"
include "eq0.mm"
include "eubii.mm"
include "mpbi.mm"
include "eleq2.mm"
include "notbid.mm"
include "albidv.mm"
include "iota2.mm"
include "mp2an.mm"
include "noel.mm"
include "mpgbi.mm"
include "eqcomi.mm"

theorem bj-nuliota
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- (/) = ( iota x A. y -. y e. x )

  proof
    vy
    vx
    wel
    #
    wn
    #
    vy
    wal
    #
    vx
    cio
    #
    c0
    vy
    cv
    #
    c0
    wcel
    #
    wn
    #
    @3
    c0
    wceq
    #
    vy
    c0
    cvv
    wcel
    @2
    vx
    weu
    #
    @6
    vy
    wal
    #
    @7
    wb
    0ex
    vx
    cv
    #
    c0
    wceq
    #
    vx
    weu
    @8
    vx
    c0
    0ex
    eueq1
    @11
    @2
    vx
    vy
    @10
    eq0
    eubii
    mpbi
    @2
    @9
    vx
    c0
    cvv
    @11
    @1
    @6
    vy
    @11
    @0
    @5
    @10
    c0
    @4
    eleq2
    notbid
    albidv
    iota2
    mp2an
    @4
    noel
    mpgbi
    eqcomi
end
