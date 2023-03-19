include "wi3.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "dfi3b.mm"
include "ran.mm"
include "anass.mm"
include "comor1.mm"
include "comcom2.mm"
include "comor2.mm"
include "com2an.mm"
include "com2or.mm"
include "leao4.mm"
include "lecom.mm"
include "comcom.mm"
include "fh1r.mm"
include "wf.mm"
include "anabs.mm"
include "oran.mm"
include "lan.mm"
include "dff.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "2or.mm"
include "or0.mm"
include "3tr.mm"
include "df2le2.mm"

theorem u3lem15
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ^ ( a v b ) ) = ( ( a ' v b ) ^ ( a v ( a ' ^ b ) ) )

  proof
    wva
    wvb
    wi3
    #
    wva
    wvb
    wo
    #
    wa
    wva
    wn
    #
    wvb
    wo
    #
    wva
    @2
    wvb
    wn
    #
    wa
    #
    wo
    #
    @2
    wvb
    wa
    #
    wo
    #
    wa
    #
    @1
    wa
    @3
    @8
    @1
    wa
    #
    wa
    @3
    wva
    @7
    wo
    #
    wa
    @0
    @9
    @1
    wva
    wvb
    dfi3b
    ran
    @3
    @8
    @1
    anass
    @10
    @11
    @3
    @10
    @6
    @1
    wa
    #
    @7
    @1
    wa
    #
    wo
    @11
    @1
    @6
    @7
    @1
    wva
    @5
    wva
    wvb
    comor1
    #
    @1
    @2
    @4
    @1
    wva
    @14
    comcom2
    @1
    wvb
    wva
    wvb
    comor2
    comcom2
    com2an
    #
    com2or
    @7
    @1
    @7
    @1
    wvb
    @2
    wva
    leao4
    #
    lecom
    comcom
    fh1r
    @12
    wva
    @13
    @7
    @12
    wva
    @1
    wa
    #
    @5
    @1
    wa
    #
    wo
    wva
    wf
    wo
    wva
    @1
    wva
    @5
    @14
    @15
    fh1r
    @17
    wva
    @18
    wf
    wva
    wvb
    anabs
    @18
    @5
    @5
    wn
    #
    wa
    #
    wf
    @1
    @19
    @5
    wva
    wvb
    oran
    lan
    wf
    @20
    @5
    dff
    ax-r1
    ax-r2
    2or
    wva
    or0
    3tr
    @7
    @1
    @16
    df2le2
    2or
    ax-r2
    lan
    3tr
end
