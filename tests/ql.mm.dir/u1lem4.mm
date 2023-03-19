include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i1.mm"
include "comid.mm"
include "comcom2.mm"
include "u1lemc1.mm"
include "fh4.mm"
include "wt.mm"
include "ax-a2.mm"
include "df-t.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "u1lemona.mm"
include "ancom.mm"
include "lor.mm"
include "lan.mm"
include "u1lem3.mm"
include "coman1.mm"
include "coman2.mm"
include "fh2.mm"
include "anass.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r5.mm"
include "2an.mm"
include "an1.mm"

theorem u1lem4
  param wva: term a
  param wvb: term b


  assert |- ( a ->1 ( a ->1 ( b ->1 a ) ) ) = ( a ->1 ( b ->1 a ) )

  proof
    wva
    wva
    wvb
    wva
    wi1
    #
    wi1
    #
    wi1
    wva
    wn
    #
    wva
    @1
    wa
    wo
    #
    @1
    wva
    @1
    df-i1
    @3
    @2
    wva
    wo
    #
    @2
    @1
    wo
    #
    wa
    #
    @1
    wva
    @2
    @1
    wva
    wva
    wva
    comid
    comcom2
    wva
    @0
    u1lemc1
    fh4
    @6
    wt
    @1
    wa
    #
    @1
    @4
    wt
    @5
    @1
    @4
    wva
    @2
    wo
    #
    wt
    @2
    wva
    ax-a2
    wt
    @8
    wva
    df-t
    ax-r1
    ax-r2
    @5
    @1
    @2
    wo
    #
    @1
    @2
    @1
    ax-a2
    @9
    @2
    wva
    @0
    wa
    #
    wo
    #
    @1
    wva
    @0
    u1lemona
    @11
    @2
    wva
    wvb
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    @1
    @10
    @15
    @2
    @0
    @14
    wva
    @0
    @12
    wvb
    wva
    wa
    #
    wo
    @14
    wvb
    wva
    df-i1
    @17
    @13
    @12
    wvb
    wva
    ancom
    lor
    ax-r2
    lan
    lor
    @1
    @16
    @1
    @2
    @13
    wva
    @12
    wa
    #
    wo
    #
    wo
    @16
    wva
    wvb
    u1lem3
    @19
    @15
    @2
    @15
    @19
    @15
    wva
    @13
    @12
    wo
    #
    wa
    #
    @19
    @14
    @20
    wva
    @12
    @13
    ax-a2
    lan
    @21
    wva
    @13
    wa
    #
    @18
    wo
    @19
    @13
    wva
    @12
    wva
    wvb
    coman1
    @13
    wvb
    wva
    wvb
    coman2
    comcom2
    fh2
    @22
    @13
    @18
    @22
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @13
    @24
    @22
    wva
    wva
    wvb
    anass
    ax-r1
    @23
    wva
    wvb
    wva
    anidm
    ran
    ax-r2
    ax-r5
    ax-r2
    ax-r2
    ax-r1
    lor
    ax-r2
    ax-r1
    ax-r2
    ax-r2
    ax-r2
    2an
    @7
    @1
    wt
    wa
    @1
    wt
    @1
    ancom
    @1
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
