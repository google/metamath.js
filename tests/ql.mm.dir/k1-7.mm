include "wn.mm"
include "wa.mm"
include "wo.mm"
include "anor3.mm"
include "cm.mm"
include "ax-a1.mm"
include "lan.mm"
include "ror.mm"
include "orcom.mm"
include "3tr.mm"
include "con4.mm"
include "oran3.mm"
include "oran2.mm"
include "2an.mm"
include "3tr1.mm"
include "ran.mm"
include "lor.mm"
include "anass.mm"
include "tr.mm"
include "ancom.mm"
include "ax-a2.mm"
include "anabs.mm"

theorem k1-7
  let wvc: term c
  let wvx: term x
  assume k1-7.1: |- x = ( ( x ^ c ) v ( x ^ c ' ) )


  assert |- ( x ' ^ c ' ) = ( ( x ' v c ) ^ c ' )

  proof
    wvx
    wn
    #
    wvc
    wn
    #
    wa
    @0
    @1
    wn
    #
    wo
    #
    @0
    @1
    wo
    #
    wa
    #
    @1
    wa
    #
    @0
    wvc
    wo
    #
    @4
    @1
    wa
    #
    wa
    #
    @7
    @1
    wa
    @0
    @5
    @1
    wvx
    @1
    wa
    #
    wvx
    @2
    wa
    #
    wo
    #
    wn
    #
    @10
    wn
    #
    @11
    wn
    #
    wa
    #
    @0
    @5
    @16
    @13
    @10
    @11
    anor3
    cm
    wvx
    @12
    wvx
    wvx
    wvc
    wa
    #
    @10
    wo
    @11
    @10
    wo
    @12
    k1-7.1
    @17
    @11
    @10
    wvc
    @2
    wvx
    wvc
    ax-a1
    #
    lan
    ror
    @11
    @10
    orcom
    3tr
    con4
    @3
    @14
    @4
    @15
    wvx
    @1
    oran3
    wvx
    @1
    oran2
    2an
    3tr1
    ran
    @6
    @7
    @4
    wa
    #
    @1
    wa
    #
    @9
    @20
    @6
    @19
    @5
    @1
    @7
    @3
    @4
    wvc
    @2
    @0
    @18
    lor
    ran
    ran
    cm
    @7
    @4
    @1
    anass
    tr
    @8
    @1
    @7
    @8
    @1
    @4
    wa
    @1
    @1
    @0
    wo
    #
    wa
    @1
    @4
    @1
    ancom
    @4
    @21
    @1
    @0
    @1
    ax-a2
    lan
    @1
    @0
    anabs
    3tr
    lan
    3tr
end
