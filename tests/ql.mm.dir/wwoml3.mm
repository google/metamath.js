include "wf.mm"
include "wo.mm"
include "tb.mm"
include "wn.mm"
include "wa.mm"
include "wt.mm"
include "ax-r1.mm"
include "ancom.mm"
include "ax-r2.mm"
include "lor.mm"
include "rbi.mm"
include "or0.mm"
include "wwoml2.mm"
include "3tr2.mm"

theorem wwoml3
  param wva: term a
  param wvb: term b
  assume wwoml3.1: |- a =< b
  assume wwoml3.2: |- ( b ^ a ' ) = 0


  assert |- ( a == b ) = 1

  proof
    wva
    wf
    wo
    #
    wvb
    tb
    wva
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    wvb
    tb
    wva
    wvb
    tb
    wt
    @0
    @3
    wvb
    wf
    @2
    wva
    wf
    wvb
    @1
    wa
    #
    @2
    @4
    wf
    wwoml3.2
    ax-r1
    wvb
    @1
    ancom
    ax-r2
    lor
    rbi
    @0
    wva
    wvb
    wva
    or0
    rbi
    wva
    wvb
    wwoml3.1
    wwoml2
    3tr2
end
