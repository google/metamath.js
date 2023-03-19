include "tb.mm"
include "wa.mm"
include "ancom.mm"
include "wn.mm"
include "wo.mm"
include "dfb.mm"
include "lan.mm"
include "coman1.mm"
include "comcom.mm"
include "comcom2.mm"
include "comcom5.mm"
include "fh1.mm"
include "wf.mm"
include "or0.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r1.mm"
include "anass.mm"
include "ax-r2.mm"
include "an0.mm"
include "dff.mm"
include "3tr2.mm"
include "2or.mm"
include "lea.mm"
include "bltr.mm"

theorem oml4
  let wva: term a
  let wvb: term b


  assert |- ( ( a == b ) ^ a ) =< b

  proof
    wva
    wvb
    tb
    #
    wva
    wa
    #
    wvb
    wva
    wa
    #
    wvb
    @1
    wva
    @0
    wa
    #
    @2
    @0
    wva
    ancom
    @3
    wva
    wva
    wvb
    wa
    #
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
    wa
    #
    @2
    @0
    @8
    wva
    wva
    wvb
    dfb
    lan
    @9
    wva
    @4
    wa
    #
    wva
    @7
    wa
    #
    wo
    #
    @2
    wva
    @4
    @7
    @4
    wva
    wva
    wvb
    coman1
    comcom
    wva
    @7
    @5
    @7
    @7
    @5
    @5
    @6
    coman1
    comcom
    comcom2
    comcom5
    fh1
    @4
    wf
    wo
    @4
    @12
    @2
    @4
    or0
    @4
    @10
    wf
    @11
    @4
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @10
    @14
    @4
    @13
    wva
    wvb
    wva
    anidm
    ran
    ax-r1
    wva
    wva
    wvb
    anass
    ax-r2
    wf
    wva
    @5
    wa
    #
    @6
    wa
    #
    @11
    @6
    wf
    wa
    wf
    @6
    wa
    wf
    @16
    @6
    wf
    ancom
    @6
    an0
    wf
    @15
    @6
    wva
    dff
    ran
    3tr2
    wva
    @5
    @6
    anass
    ax-r2
    2or
    wva
    wvb
    ancom
    3tr2
    ax-r2
    ax-r2
    ax-r2
    wvb
    wva
    lea
    bltr
end
