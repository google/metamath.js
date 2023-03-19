include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "elin.mm"
include "imbi2i.mm"
include "albii.mm"
include "jcab.mm"
include "19.26.mm"
include "3bitrri.mm"
include "dfss2.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem ssin
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A C_ B /\ A C_ C ) <-> A C_ ( B i^i C ) )

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
    #
    @1
    @0
    cC
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    @1
    @0
    cB
    cC
    cin
    #
    wcel
    #
    wi
    #
    vx
    wal
    #
    cA
    cB
    wss
    #
    cA
    cC
    wss
    #
    wa
    cA
    @9
    wss
    @12
    @1
    @2
    @5
    wa
    #
    wi
    #
    vx
    wal
    @3
    @6
    wa
    #
    vx
    wal
    @8
    @11
    @16
    vx
    @10
    @15
    @1
    @0
    cB
    cC
    elin
    imbi2i
    albii
    @16
    @17
    vx
    @1
    @2
    @5
    jcab
    albii
    @3
    @6
    vx
    19.26
    3bitrri
    @13
    @4
    @14
    @7
    vx
    cA
    cB
    dfss2
    vx
    cA
    cC
    dfss2
    anbi12i
    vx
    cA
    @9
    dfss2
    3bitr4i
end
