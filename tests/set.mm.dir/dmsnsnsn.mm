include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cdm.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "vex.mm"
include "opid.mm"
include "sneq.mm"
include "sneqd.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "eqeq12d.mm"
include "dmsnop.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "0ex.mm"
include "snid.mm"
include "dmsn0el.mm"
include "ax-mp.mm"
include "snprc.mm"
include "biimpi.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem dmsnsnsn
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- dom { { { A } } } = { A }

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    csn
    #
    csn
    #
    cdm
    #
    @1
    wceq
    #
    vx
    cv
    #
    @6
    cop
    #
    csn
    #
    cdm
    #
    @6
    csn
    #
    wceq
    @5
    vx
    cA
    cvv
    @6
    cA
    wceq
    #
    @9
    @4
    @10
    @1
    @11
    @8
    @3
    @11
    @7
    @2
    @11
    @7
    @10
    csn
    @2
    @6
    vx
    vex
    #
    opid
    @11
    @10
    @1
    @6
    cA
    sneq
    #
    sneqd
    syl5eq
    sneqd
    dmeqd
    @13
    eqeq12d
    @6
    @6
    @12
    dmsnop
    vtoclg
    @0
    wn
    #
    c0
    csn
    #
    csn
    #
    cdm
    #
    c0
    @4
    @1
    c0
    @15
    wcel
    @17
    c0
    wceq
    c0
    0ex
    snid
    @15
    dmsn0el
    ax-mp
    @14
    @3
    @16
    @14
    @2
    @15
    @14
    @1
    c0
    @14
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    #
    sneqd
    sneqd
    dmeqd
    @18
    3eqtr4a
    pm2.61i
end
