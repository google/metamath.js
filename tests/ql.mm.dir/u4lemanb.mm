include "wi4.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "df-i4.mm"
include "ran.mm"
include "comanr2.mm"
include "comcom3.mm"
include "com2or.mm"
include "comorr2.mm"
include "comid.mm"
include "com2an.mm"
include "fh1r.mm"
include "ax-a2.mm"
include "wf.mm"
include "anass.mm"
include "anidm.mm"
include "lan.mm"
include "ax-r2.mm"
include "dff.mm"
include "ax-r1.mm"
include "an0.mm"
include "2or.mm"
include "or0.mm"

theorem u4lemanb
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->4 b ) ^ b ' ) = ( ( a ' v b ) ^ b ' )

  proof
    wva
    wvb
    wi4
    #
    wvb
    wn
    #
    wa
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
    @3
    wvb
    wo
    #
    @1
    wa
    #
    wo
    #
    @1
    wa
    #
    @7
    @0
    @8
    @1
    wva
    wvb
    df-i4
    ran
    @9
    @5
    @1
    wa
    #
    @7
    @1
    wa
    #
    wo
    #
    @7
    @1
    @5
    @7
    @1
    @2
    @4
    wvb
    @2
    wva
    wvb
    comanr2
    comcom3
    #
    wvb
    @4
    @3
    wvb
    comanr2
    comcom3
    #
    com2or
    @1
    @6
    @1
    wvb
    @6
    @3
    wvb
    comorr2
    comcom3
    @1
    comid
    com2an
    fh1r
    @12
    @11
    @10
    wo
    #
    @7
    @10
    @11
    ax-a2
    @15
    @7
    wf
    wo
    @7
    @11
    @7
    @10
    wf
    @11
    @6
    @1
    @1
    wa
    #
    wa
    @7
    @6
    @1
    @1
    anass
    @16
    @1
    @6
    @1
    anidm
    lan
    ax-r2
    @10
    @2
    @1
    wa
    #
    @4
    @1
    wa
    #
    wo
    #
    wf
    @1
    @2
    @4
    @13
    @14
    fh1r
    @19
    wf
    wf
    wo
    wf
    @17
    wf
    @18
    wf
    @17
    wva
    wvb
    @1
    wa
    #
    wa
    #
    wf
    wva
    wvb
    @1
    anass
    @21
    wva
    wf
    wa
    #
    wf
    @22
    @21
    wf
    @20
    wva
    wvb
    dff
    #
    lan
    ax-r1
    wva
    an0
    ax-r2
    ax-r2
    @18
    @3
    @20
    wa
    #
    wf
    @3
    wvb
    @1
    anass
    @24
    @3
    wf
    wa
    #
    wf
    @25
    @24
    wf
    @20
    @3
    @23
    lan
    ax-r1
    @3
    an0
    ax-r2
    ax-r2
    2or
    wf
    or0
    ax-r2
    ax-r2
    2or
    @7
    or0
    ax-r2
    ax-r2
    ax-r2
    ax-r2
end
