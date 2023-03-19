include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "wn.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "iman.mm"
include "eldif.mm"
include "xchbinxr.mm"
include "albii.mm"
include "dfss2.mm"
include "eq0.mm"
include "3bitr4i.mm"

theorem ssdif0
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ B <-> ( A \ B ) = (/) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wi
    #
    vx
    wal
    @0
    cA
    cB
    cdif
    #
    wcel
    #
    wn
    #
    vx
    wal
    cA
    cB
    wss
    @4
    c0
    wceq
    @3
    @6
    vx
    @3
    @1
    @2
    wn
    wa
    @5
    @1
    @2
    iman
    @0
    cA
    cB
    eldif
    xchbinxr
    albii
    vx
    cA
    cB
    dfss2
    vx
    @4
    eq0
    3bitr4i
end
