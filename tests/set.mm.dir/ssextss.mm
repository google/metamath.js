include "wss.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "sspwb.mm"
include "dfss2.mm"
include "selpw.mm"
include "imbi12i.mm"
include "albii.mm"
include "3bitri.mm"

theorem ssextss
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B <-> A. x ( x C_ A -> x C_ B ) )

  proof
    cA
    cB
    wss
    cA
    cpw
    #
    cB
    cpw
    #
    wss
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wi
    #
    vx
    wal
    @2
    cA
    wss
    #
    @2
    cB
    wss
    #
    wi
    #
    vx
    wal
    cA
    cB
    sspwb
    vx
    @0
    @1
    dfss2
    @5
    @8
    vx
    @3
    @6
    @4
    @7
    vx
    cA
    selpw
    vx
    cB
    selpw
    imbi12i
    albii
    3bitri
end
