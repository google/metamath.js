include "wcel.mm"
include "wceq.mm"
include "wsbc.mm"
include "cv.mm"
include "csb.mm"
include "wb.mm"
include "wal.mm"
include "dfcleq.mm"
include "sbcth.mm"
include "sbcbig.mm"
include "mpbid.mm"
include "sbcal.mm"
include "syl6bb.mm"
include "albidv.mm"
include "sbcel2.mm"
include "a1i.mm"
include "bibi12d.mm"
include "3bitrd.mm"
include "syl6bbr.mm"

theorem bj-sbceqgALT
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> ( [. A / x ]. B = C <-> [_ A / x ]_ B = [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cC
    wceq
    #
    vx
    cA
    wsbc
    #
    vy
    cv
    #
    vx
    cA
    cB
    csb
    #
    wcel
    #
    @3
    vx
    cA
    cC
    csb
    #
    wcel
    #
    wb
    #
    vy
    wal
    #
    @4
    @6
    wceq
    @0
    @2
    @3
    cB
    wcel
    #
    @3
    cC
    wcel
    #
    wb
    #
    vx
    cA
    wsbc
    #
    vy
    wal
    #
    @10
    vx
    cA
    wsbc
    #
    @11
    vx
    cA
    wsbc
    #
    wb
    #
    vy
    wal
    @9
    @0
    @2
    @12
    vy
    wal
    #
    vx
    cA
    wsbc
    #
    @14
    @0
    @1
    @18
    wb
    #
    vx
    cA
    wsbc
    @2
    @19
    wb
    @20
    vx
    cA
    cV
    vy
    cB
    cC
    dfcleq
    sbcth
    @1
    @18
    vx
    cA
    cV
    sbcbig
    mpbid
    @12
    vy
    vx
    cA
    sbcal
    syl6bb
    @0
    @13
    @17
    vy
    @10
    @11
    vx
    cA
    cV
    sbcbig
    albidv
    @0
    @17
    @8
    vy
    @0
    @15
    @5
    @16
    @7
    @15
    @5
    wb
    @0
    vx
    cA
    @3
    cB
    sbcel2
    a1i
    @16
    @7
    wb
    @0
    vx
    cA
    @3
    cC
    sbcel2
    a1i
    bibi12d
    albidv
    3bitrd
    vy
    @4
    @6
    dfcleq
    syl6bbr
end
