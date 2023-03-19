include "wa.mm"
include "wn.mm"
include "wi1.mm"
include "wo.mm"
include "wf.mm"
include "df-i1.mm"
include "lan.mm"
include "lear.mm"
include "lelor.mm"
include "lelan.mm"
include "oran3.mm"
include "dff.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "lbtr.mm"
include "le0.mm"
include "lebi.mm"

theorem go1
  let wva: term a
  let wvb: term b


  assert |- ( ( a ^ b ) ^ ( a ->1 b ' ) ) = 0

  proof
    wva
    wvb
    wa
    #
    wva
    wvb
    wn
    #
    wi1
    #
    wa
    @0
    wva
    wn
    #
    wva
    @1
    wa
    #
    wo
    #
    wa
    #
    wf
    @2
    @5
    @0
    wva
    @1
    df-i1
    lan
    @6
    wf
    @6
    @0
    @3
    @1
    wo
    #
    wa
    #
    wf
    @5
    @7
    @0
    @4
    @1
    @3
    wva
    @1
    lear
    lelor
    lelan
    @8
    @0
    @0
    wn
    #
    wa
    #
    wf
    @7
    @9
    @0
    wva
    wvb
    oran3
    lan
    wf
    @10
    @0
    dff
    ax-r1
    ax-r2
    lbtr
    @6
    le0
    lebi
    ax-r2
end
