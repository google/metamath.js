include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "csb.mm"
include "wss.mm"
include "sbcal.mm"
include "sbcimg.mm"
include "sbcel2.mm"
include "imbi12i.mm"
include "syl6bb.mm"
include "albidv.mm"
include "syl5bb.mm"
include "dfss2.mm"
include "sbcbii.mm"
include "3bitr4g.mm"

theorem sbcssg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> ( [. A / x ]. B C_ C <-> [_ A / x ]_ B C_ [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    @1
    cC
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
    cB
    csb
    #
    wcel
    #
    @1
    vx
    cA
    cC
    csb
    #
    wcel
    #
    wi
    #
    vy
    wal
    #
    cB
    cC
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
    cV
    sbcimg
    @15
    @8
    @16
    @10
    vx
    cA
    @1
    cB
    sbcel2
    vx
    cA
    @1
    cC
    sbcel2
    imbi12i
    syl6bb
    albidv
    syl5bb
    @13
    @5
    vx
    cA
    vy
    cB
    cC
    dfss2
    sbcbii
    vy
    @7
    @9
    dfss2
    3bitr4g
end
