include "wf.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "wr1.mm"
include "ancom.mm"
include "bi1.mm"
include "wr2.mm"
include "wlor.mm"
include "or0.mm"
include "wom4.mm"
include "w3tr2.mm"

theorem wom5
  let wva: term a
  let wvb: term b
  assume wom5.1: |- ( a =<2 b ) = 1
  assume wom5.2: |- ( ( b ^ a ' ) == 0 ) = 1


  assert |- ( a == b ) = 1

  proof
    wva
    wf
    wo
    #
    wva
    wva
    wn
    #
    wvb
    wa
    #
    wo
    wva
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
    @3
    wf
    wom5.2
    wr1
    @3
    @2
    wvb
    @1
    ancom
    bi1
    wr2
    wlor
    @0
    wva
    wva
    or0
    bi1
    wva
    wvb
    wom5.1
    wom4
    w3tr2
end
