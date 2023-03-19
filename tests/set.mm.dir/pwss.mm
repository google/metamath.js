include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "dfss2.mm"
include "selpw.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitri.mm"

theorem pwss
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ~P A C_ B <-> A. x ( x C_ A -> x e. B ) )

  proof
    cA
    cpw
    #
    cB
    wss
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cB
    wcel
    #
    wi
    #
    vx
    wal
    @1
    cA
    wss
    #
    @3
    wi
    #
    vx
    wal
    vx
    @0
    cB
    dfss2
    @4
    @6
    vx
    @2
    @5
    @3
    vx
    cA
    selpw
    imbi1i
    albii
    bitri
end
