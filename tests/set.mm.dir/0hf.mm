include "c0.mm"
include "chf.mm"
include "wcel.mm"
include "cv.mm"
include "cr1.mm"
include "cfv.mm"
include "com.mm"
include "wrex.mm"
include "csuc.mm"
include "peano1.mm"
include "peano2.mm"
include "ax-mp.mm"
include "cpw.mm"
include "0elpw.mm"
include "con0.mm"
include "wceq.mm"
include "0elon.mm"
include "r1suc.mm"
include "eleqtrri.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "elhf.mm"
include "mpbir.mm"

theorem 0hf
  let vx: setvar x


  assert |- (/) e. Hf

  proof
    c0
    chf
    wcel
    c0
    vx
    cv
    #
    cr1
    cfv
    #
    wcel
    #
    vx
    com
    wrex
    #
    c0
    csuc
    #
    com
    wcel
    #
    c0
    @4
    cr1
    cfv
    #
    wcel
    #
    @3
    c0
    com
    wcel
    @5
    peano1
    c0
    peano2
    ax-mp
    c0
    c0
    cr1
    cfv
    #
    cpw
    #
    @6
    @8
    0elpw
    c0
    con0
    wcel
    @6
    @9
    wceq
    0elon
    c0
    r1suc
    ax-mp
    eleqtrri
    @2
    @7
    vx
    @4
    com
    @0
    @4
    wceq
    @1
    @6
    c0
    @0
    @4
    cr1
    fveq2
    eleq2d
    rspcev
    mp2an
    vx
    c0
    elhf
    mpbir
end
