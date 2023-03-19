include "wi4.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "df-i4.mm"
include "wf.mm"
include "ud4lem3a.mm"
include "lor.mm"
include "comid.mm"
include "comcom2.mm"
include "comor1.mm"
include "comor2.mm"
include "com2an.mm"
include "com2or.mm"
include "comcom.mm"
include "bctr.mm"
include "fh4r.mm"
include "ancom.mm"
include "wt.mm"
include "ax-a2.mm"
include "ud4lem3b.mm"
include "ax-r2.mm"
include "df-t.mm"
include "ax-r1.mm"
include "2an.mm"
include "an1.mm"
include "ran.mm"
include "dff.mm"
include "2or.mm"
include "or0.mm"

theorem ud4lem3
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->4 b ) ->4 ( a v b ) ) = ( a v b )

  proof
    wva
    wvb
    wi4
    #
    wva
    wvb
    wo
    #
    wi4
    @0
    @1
    wa
    #
    @0
    wn
    #
    @1
    wa
    #
    wo
    #
    @3
    @1
    wo
    #
    @1
    wn
    #
    wa
    #
    wo
    #
    @1
    @0
    @1
    df-i4
    @9
    @1
    wf
    wo
    @1
    @5
    @1
    @8
    wf
    @5
    @2
    @3
    wo
    #
    @1
    @4
    @3
    @2
    wva
    wvb
    ud4lem3a
    lor
    @10
    @0
    @3
    wo
    #
    @1
    @3
    wo
    #
    wa
    #
    @1
    @0
    @3
    @1
    @0
    @0
    @0
    comid
    comcom2
    @0
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    @15
    wvb
    wo
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    @1
    wva
    wvb
    df-i4
    @1
    @21
    @1
    @17
    @20
    @1
    @14
    @16
    @1
    wva
    wvb
    wva
    wvb
    comor1
    #
    wva
    wvb
    comor2
    #
    com2an
    @1
    @15
    wvb
    @1
    wva
    @22
    comcom2
    #
    @23
    com2an
    com2or
    @1
    @18
    @19
    @1
    @15
    wvb
    @24
    @23
    com2or
    @1
    wvb
    @23
    comcom2
    com2an
    com2or
    comcom
    bctr
    fh4r
    @13
    @12
    @11
    wa
    #
    @1
    @11
    @12
    ancom
    @25
    @1
    wt
    wa
    @1
    @12
    @1
    @11
    wt
    @12
    @6
    @1
    @1
    @3
    ax-a2
    wva
    wvb
    ud4lem3b
    #
    ax-r2
    wt
    @11
    @0
    df-t
    ax-r1
    2an
    @1
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r2
    @8
    @1
    @7
    wa
    #
    wf
    @6
    @1
    @7
    @26
    ran
    wf
    @27
    @1
    dff
    ax-r1
    ax-r2
    2or
    @1
    or0
    ax-r2
    ax-r2
end
