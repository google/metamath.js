include "cun.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "dfss2.mm"
include "19.26.mm"
include "wo.mm"
include "elun.mm"
include "imbi1i.mm"
include "jaob.mm"
include "bitri.mm"
include "albii.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "bitr2i.mm"

theorem unss
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A C_ C /\ B C_ C ) <-> ( A u. B ) C_ C )

  proof
    cA
    cB
    cun
    #
    cC
    wss
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cC
    wcel
    #
    wi
    #
    vx
    wal
    #
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    #
    vx
    @0
    cC
    dfss2
    @1
    cA
    wcel
    #
    @3
    wi
    #
    @1
    cB
    wcel
    #
    @3
    wi
    #
    wa
    #
    vx
    wal
    @10
    vx
    wal
    #
    @12
    vx
    wal
    #
    wa
    @5
    @8
    @10
    @12
    vx
    19.26
    @4
    @13
    vx
    @4
    @9
    @11
    wo
    #
    @3
    wi
    @13
    @2
    @16
    @3
    @1
    cA
    cB
    elun
    imbi1i
    @9
    @3
    @11
    jaob
    bitri
    albii
    @6
    @14
    @7
    @15
    vx
    cA
    cC
    dfss2
    vx
    cB
    cC
    dfss2
    anbi12i
    3bitr4i
    bitr2i
end
