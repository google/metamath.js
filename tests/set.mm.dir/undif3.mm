include "cdif.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "elun.mm"
include "pm4.53.mm"
include "eldif.mm"
include "xchnxbir.mm"
include "anbi12i.mm"
include "orbi2i.mm"
include "ordi.mm"
include "orcom.mm"
include "anbi2i.mm"
include "bitri.mm"
include "3bitri.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem undif3
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A u. ( B \ C ) ) = ( ( A u. B ) \ ( C \ A ) )

  proof
    vx
    cA
    cB
    cC
    cdif
    #
    cun
    #
    cA
    cB
    cun
    #
    cC
    cA
    cdif
    #
    cdif
    #
    vx
    cv
    #
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wn
    #
    wa
    @5
    cA
    wcel
    #
    @5
    cB
    wcel
    #
    wo
    #
    @5
    cC
    wcel
    #
    wn
    #
    @9
    wo
    #
    wa
    #
    @5
    @4
    wcel
    @5
    @1
    wcel
    #
    @6
    @11
    @8
    @14
    @5
    cA
    cB
    elun
    @12
    @9
    wn
    wa
    @14
    @7
    @12
    @9
    pm4.53
    @5
    cC
    cA
    eldif
    xchnxbir
    anbi12i
    @5
    @2
    @3
    eldif
    @16
    @9
    @5
    @0
    wcel
    #
    wo
    @9
    @10
    @13
    wa
    #
    wo
    #
    @15
    @5
    cA
    @0
    elun
    @17
    @18
    @9
    @5
    cB
    cC
    eldif
    orbi2i
    @19
    @11
    @9
    @13
    wo
    #
    wa
    @15
    @9
    @10
    @13
    ordi
    @20
    @14
    @11
    @9
    @13
    orcom
    anbi2i
    bitri
    3bitri
    3bitr4ri
    eqriv
end
