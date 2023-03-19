include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "csb.mm"
include "wss.mm"
include "sbcal.mm"
include "sbcimg.mm"
include "wb.mm"
include "sbcel2.mm"
include "a1i.mm"
include "imbi12d.mm"
include "bitrd.mm"
include "albidv.mm"
include "syl5bb.mm"
include "dfss2.mm"
include "sbcbii.mm"
include "3bitr4g.mm"

theorem sbcssOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y


  assert |- ( A e. B -> ( [. A / x ]. C C_ D <-> [_ A / x ]_ C C_ [_ A / x ]_ D ) )

  proof
    cA
    cB
    wcel
    #
    vy
    cv
    #
    cC
    wcel
    #
    @1
    cD
    wcel
    #
    wi
    #
    vy
    wal
    #
    vx
    cA
    wsbc
    #
    @1
    vx
    cA
    cC
    csb
    #
    wcel
    #
    @1
    vx
    cA
    cD
    csb
    #
    wcel
    #
    wi
    #
    vy
    wal
    #
    cC
    cD
    wss
    #
    vx
    cA
    wsbc
    @7
    @9
    wss
    @6
    @4
    vx
    cA
    wsbc
    #
    vy
    wal
    @0
    @12
    @4
    vy
    vx
    cA
    sbcal
    @0
    @14
    @11
    vy
    @0
    @14
    @2
    vx
    cA
    wsbc
    #
    @3
    vx
    cA
    wsbc
    #
    wi
    @11
    @2
    @3
    vx
    cA
    cB
    sbcimg
    @0
    @15
    @8
    @16
    @10
    @15
    @8
    wb
    @0
    vx
    cA
    @1
    cC
    sbcel2
    a1i
    @16
    @10
    wb
    @0
    vx
    cA
    @1
    cD
    sbcel2
    a1i
    imbi12d
    bitrd
    albidv
    syl5bb
    @13
    @5
    vx
    cA
    vy
    cC
    cD
    dfss2
    sbcbii
    vy
    @7
    @9
    dfss2
    3bitr4g
end
