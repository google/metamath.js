include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "wn.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "elin.mm"
include "imbi1i.mm"
include "iman.mm"
include "bitri.mm"
include "eldif.mm"
include "anbi2i.mm"
include "anass.mm"
include "3bitr4ri.mm"
include "xchbinx.mm"
include "albii.mm"
include "dfss2.mm"
include "eq0.mm"
include "3bitr4i.mm"

theorem inssdif0
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A i^i B ) C_ C <-> ( A i^i ( B \ C ) ) = (/) )

  proof
    vx
    cv
    #
    cA
    cB
    cin
    #
    wcel
    #
    @0
    cC
    wcel
    #
    wi
    #
    vx
    wal
    @0
    cA
    cB
    cC
    cdif
    #
    cin
    #
    wcel
    #
    wn
    #
    vx
    wal
    @1
    cC
    wss
    @6
    c0
    wceq
    @4
    @8
    vx
    @4
    @0
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wa
    #
    @3
    wn
    #
    wa
    #
    @7
    @4
    @11
    @3
    wi
    @13
    wn
    @2
    @11
    @3
    @0
    cA
    cB
    elin
    imbi1i
    @11
    @3
    iman
    bitri
    @9
    @0
    @5
    wcel
    #
    wa
    @9
    @10
    @12
    wa
    #
    wa
    @7
    @13
    @14
    @15
    @9
    @0
    cB
    cC
    eldif
    anbi2i
    @0
    cA
    @5
    elin
    @9
    @10
    @12
    anass
    3bitr4ri
    xchbinx
    albii
    vx
    @1
    cC
    dfss2
    vx
    @6
    eq0
    3bitr4i
end
