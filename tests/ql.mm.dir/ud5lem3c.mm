include "wi5.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "ud5lem0c.mm"
include "oran.mm"
include "con2.mm"
include "anor2.mm"
include "lan.mm"
include "ax-r2.mm"
include "2an.mm"
include "an32.mm"
include "an4.mm"
include "ancom.mm"
include "anabs.mm"
include "anidm.mm"
include "ran.mm"
include "anass.mm"
include "ax-r1.mm"

theorem ud5lem3c
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->5 b ) ' ^ ( a v ( a ' ^ b ) ) ' ) = ( ( ( a v b ) ^ ( a v b ' ) ) ^ a ' )

  proof
    wva
    wvb
    wi5
    wn
    #
    wva
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    wn
    #
    wa
    @1
    wvb
    wn
    #
    wo
    #
    wva
    @5
    wo
    #
    wa
    #
    wva
    wvb
    wo
    #
    wa
    #
    @1
    @7
    wa
    #
    wa
    #
    @9
    @7
    wa
    @1
    wa
    #
    @0
    @10
    @4
    @11
    wva
    wvb
    ud5lem0c
    @4
    @1
    @2
    wn
    #
    wa
    #
    @11
    @3
    @15
    wva
    @2
    oran
    con2
    @14
    @7
    @1
    @2
    @7
    wva
    wvb
    anor2
    con2
    lan
    ax-r2
    2an
    @12
    @8
    @11
    wa
    #
    @9
    wa
    #
    @13
    @8
    @9
    @11
    an32
    @17
    @9
    @7
    @1
    wa
    #
    wa
    #
    @13
    @17
    @18
    @9
    wa
    @19
    @16
    @18
    @9
    @16
    @6
    @1
    wa
    #
    @7
    @7
    wa
    #
    wa
    #
    @18
    @6
    @7
    @1
    @7
    an4
    @22
    @11
    @18
    @20
    @1
    @21
    @7
    @20
    @1
    @6
    wa
    @1
    @6
    @1
    ancom
    @1
    @5
    anabs
    ax-r2
    @7
    anidm
    2an
    @1
    @7
    ancom
    ax-r2
    ax-r2
    ran
    @18
    @9
    ancom
    ax-r2
    @13
    @19
    @9
    @7
    @1
    anass
    ax-r1
    ax-r2
    ax-r2
    ax-r2
end
