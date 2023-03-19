include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wss.mm"
include "wb.mm"
include "velsn.mm"
include "imbi1i.mm"
include "albii.mm"
include "a1i.mm"
include "dfss2.mm"
include "clel2g.mm"
include "3bitr4rd.mm"

theorem snssg
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. B <-> { A } C_ B ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cv
    #
    cA
    csn
    #
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
    #
    @1
    cA
    wceq
    #
    @4
    wi
    #
    vx
    wal
    #
    @2
    cB
    wss
    #
    cA
    cB
    wcel
    @6
    @9
    wb
    @0
    @5
    @8
    vx
    @3
    @7
    @4
    vx
    cA
    velsn
    imbi1i
    albii
    a1i
    @10
    @6
    wb
    @0
    vx
    @2
    cB
    dfss2
    a1i
    vx
    cA
    cB
    cV
    clel2g
    3bitr4rd
end
