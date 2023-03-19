include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cvv.mm"
include "cdif.mm"
include "wss.mm"
include "wn.mm"
include "con34b.mm"
include "compel.mm"
include "imbi12i.mm"
include "bitr4i.mm"
include "albii.mm"
include "dfss2.mm"
include "3bitr4i.mm"

theorem conss34OLD
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A C_ B <-> ( _V \ B ) C_ ( _V \ A ) )

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
    cvv
    cB
    cdif
    #
    wcel
    #
    @0
    cvv
    cA
    cdif
    #
    wcel
    #
    wi
    #
    vx
    wal
    cA
    cB
    wss
    @4
    @6
    wss
    @3
    @8
    vx
    @3
    @2
    wn
    #
    @1
    wn
    #
    wi
    @8
    @1
    @2
    con34b
    @5
    @9
    @7
    @10
    vx
    cB
    compel
    vx
    cA
    compel
    imbi12i
    bitr4i
    albii
    vx
    cA
    cB
    dfss2
    vx
    @4
    @6
    dfss2
    3bitr4i
end
