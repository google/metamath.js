include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wb.mm"
include "dfss2.mm"
include "wa.mm"
include "pm5.44.mm"
include "eldif.mm"
include "imbi2i.mm"
include "syl6bbr.mm"
include "sps.mm"
include "sylbi.mm"
include "albidv.mm"
include "disj1.mm"
include "3bitr4g.mm"

theorem reldisj
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A C_ C -> ( ( A i^i B ) = (/) <-> A C_ ( C \ B ) ) )

  proof
    cA
    cC
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    @1
    cB
    wcel
    wn
    #
    wi
    #
    vx
    wal
    @2
    @1
    cC
    cB
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
    cin
    c0
    wceq
    cA
    @5
    wss
    @0
    @4
    @7
    vx
    @0
    @2
    @1
    cC
    wcel
    #
    wi
    #
    vx
    wal
    @4
    @7
    wb
    #
    vx
    cA
    cC
    dfss2
    @9
    @10
    vx
    @9
    @4
    @2
    @8
    @3
    wa
    #
    wi
    @7
    @2
    @8
    @3
    pm5.44
    @6
    @11
    @2
    @1
    cC
    cB
    eldif
    imbi2i
    syl6bbr
    sps
    sylbi
    albidv
    vx
    cA
    cB
    disj1
    vx
    cA
    @5
    dfss2
    3bitr4g
end
