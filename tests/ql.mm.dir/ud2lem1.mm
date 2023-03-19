include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i2.mm"
include "ud2lem0c.mm"
include "2an.mm"
include "2or.mm"
include "wf.mm"
include "ancom.mm"
include "lor.mm"
include "dff.mm"
include "oran.mm"
include "ax-r1.mm"
include "lan.mm"
include "ax-r2.mm"
include "anandir.mm"
include "ax-a2.mm"
include "ran.mm"
include "or0.mm"

theorem ud2lem1
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->2 b ) ->2 ( b ->2 a ) ) = ( a v ( a ' ^ b ' ) )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wva
    wi2
    #
    wi2
    @1
    @0
    wn
    #
    @1
    wn
    #
    wa
    #
    wo
    #
    wva
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @0
    @1
    df-i2
    @5
    wva
    @7
    @6
    wa
    #
    wo
    #
    @7
    wva
    wvb
    wo
    #
    wa
    #
    @6
    wvb
    wva
    wo
    #
    wa
    #
    wa
    #
    wo
    #
    @9
    @1
    @11
    @4
    @16
    wvb
    wva
    df-i2
    @2
    @13
    @3
    @15
    wva
    wvb
    ud2lem0c
    wvb
    wva
    ud2lem0c
    2an
    2or
    @17
    @9
    wf
    wo
    @9
    @11
    @9
    @16
    wf
    @10
    @8
    wva
    @7
    @6
    ancom
    lor
    wf
    @16
    wf
    @10
    @14
    wa
    #
    @16
    wf
    @10
    @10
    wn
    #
    wa
    @18
    @10
    dff
    @19
    @14
    @10
    @14
    @19
    wvb
    wva
    oran
    ax-r1
    lan
    ax-r2
    @18
    @7
    @14
    wa
    #
    @15
    wa
    @16
    @7
    @6
    @14
    anandir
    @20
    @13
    @15
    @14
    @12
    @7
    wvb
    wva
    ax-a2
    lan
    ran
    ax-r2
    ax-r2
    ax-r1
    2or
    @9
    or0
    ax-r2
    ax-r2
    ax-r2
end
