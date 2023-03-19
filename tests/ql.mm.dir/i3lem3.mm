include "wn.mm"
include "wa.mm"
include "wo.mm"
include "omlan.mm"
include "ancom.mm"
include "ax-a2.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "i3lem1.mm"
include "lor.mm"
include "orabs.mm"
include "ax-r2.mm"
include "2or.mm"
include "3tr2.mm"
include "lan.mm"
include "3tr1.mm"

theorem i3lem3
  param wva: term a
  param wvb: term b
  assume i3lem.1: |- ( a ->3 b ) = 1


  assert |- ( ( a ' v b ) ^ b ' ) = ( a ' ^ b ' )

  proof
    wvb
    wn
    #
    wvb
    @0
    wva
    wn
    #
    wa
    #
    wo
    #
    wa
    #
    @2
    @1
    wvb
    wo
    #
    @0
    wa
    #
    @1
    @0
    wa
    #
    wvb
    @1
    omlan
    @6
    @0
    @5
    wa
    @4
    @5
    @0
    ancom
    @5
    @3
    @0
    @5
    wvb
    @1
    wo
    #
    @3
    @1
    wvb
    ax-a2
    wvb
    @1
    wvb
    wa
    #
    @7
    wo
    #
    wo
    #
    wvb
    @9
    wo
    #
    @7
    wo
    #
    @8
    @3
    @13
    @11
    wvb
    @9
    @7
    ax-a3
    ax-r1
    @10
    @1
    wvb
    wva
    wvb
    i3lem.1
    i3lem1
    lor
    @12
    wvb
    @7
    @2
    @12
    wvb
    wvb
    @1
    wa
    #
    wo
    wvb
    @9
    @14
    wvb
    @1
    wvb
    ancom
    lor
    wvb
    @1
    orabs
    ax-r2
    @1
    @0
    ancom
    #
    2or
    3tr2
    ax-r2
    lan
    ax-r2
    @15
    3tr1
end
