include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wss.mm"
include "wi.mm"
include "eq0.mm"
include "wa.mm"
include "iman.mm"
include "elin.mm"
include "eldif.mm"
include "anbi2ci.mm"
include "annim.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "xchbinxr.mm"
include "ax-2.mm"
include "sylbir.mm"
include "al2imi.mm"
include "dfss2.mm"
include "3imtr4g.mm"
include "sylbi.mm"

theorem difin0ss
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( ( A \ B ) i^i C ) = (/) -> ( C C_ A -> C C_ B ) )

  proof
    cA
    cB
    cdif
    #
    cC
    cin
    #
    c0
    wceq
    vx
    cv
    #
    @1
    wcel
    #
    wn
    #
    vx
    wal
    #
    cC
    cA
    wss
    #
    cC
    cB
    wss
    #
    wi
    vx
    @1
    eq0
    @5
    @2
    cC
    wcel
    #
    @2
    cA
    wcel
    #
    wi
    #
    vx
    wal
    @8
    @2
    cB
    wcel
    #
    wi
    #
    vx
    wal
    @6
    @7
    @4
    @10
    @12
    vx
    @4
    @8
    @9
    @11
    wi
    #
    wi
    #
    @10
    @12
    wi
    @14
    @8
    @13
    wn
    #
    wa
    #
    @3
    @8
    @13
    iman
    @3
    @2
    @0
    wcel
    #
    @8
    wa
    @8
    @9
    @11
    wn
    wa
    #
    wa
    @16
    @2
    @0
    cC
    elin
    @17
    @18
    @8
    @2
    cA
    cB
    eldif
    anbi2ci
    @18
    @15
    @8
    @9
    @11
    annim
    anbi2i
    3bitri
    xchbinxr
    @8
    @9
    @11
    ax-2
    sylbir
    al2imi
    vx
    cC
    cA
    dfss2
    vx
    cC
    cB
    dfss2
    3imtr4g
    sylbi
end
