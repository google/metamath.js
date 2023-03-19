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
include "orc.mm"
include "olc.mm"
include "jca.mm"
include "anim12i.mm"
include "jaoi.mm"
include "simpl.mm"
include "orcd.mm"
include "adantr.mm"
include "adantl.mm"
include "ccase.mm"
include "impbii.mm"
include "3bitri.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem undif3OLD
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
    @15
    @9
    @15
    @18
    @9
    @11
    @14
    @9
    @10
    orc
    @9
    @13
    olc
    jca
    @10
    @11
    @13
    @14
    @10
    @9
    olc
    @13
    @9
    orc
    anim12i
    jaoi
    @9
    @13
    @10
    @9
    @19
    @9
    @13
    wa
    @9
    @18
    @9
    @13
    simpl
    orcd
    @18
    @9
    olc
    @9
    @19
    @9
    @9
    @18
    orc
    #
    adantr
    @9
    @19
    @10
    @20
    adantl
    ccase
    impbii
    3bitri
    3bitr4ri
    eqriv
end
