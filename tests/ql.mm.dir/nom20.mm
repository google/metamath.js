include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wid0.mm"
include "wi1.mm"
include "lea.mm"
include "leor.mm"
include "letr.mm"
include "lelor.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "oran3.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "lbtr.mm"
include "df2le2.mm"
include "df-id0.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom20
  param wva: term a
  param wvb: term b


  assert |- ( a ==0 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wn
    #
    wva
    wvb
    wa
    #
    wo
    #
    @1
    wn
    #
    wva
    wo
    #
    wa
    @2
    wva
    @1
    wid0
    wva
    wvb
    wi1
    @2
    @4
    @2
    @0
    wvb
    wn
    #
    wva
    wo
    #
    wo
    #
    @4
    @1
    @6
    @0
    @1
    wva
    @6
    wva
    wvb
    lea
    wva
    @5
    leor
    letr
    lelor
    @7
    @0
    @5
    wo
    #
    wva
    wo
    #
    @4
    @9
    @7
    @0
    @5
    wva
    ax-a3
    ax-r1
    @8
    @3
    wva
    wva
    wvb
    oran3
    ax-r5
    ax-r2
    lbtr
    df2le2
    wva
    @1
    df-id0
    wva
    wvb
    df-i1
    3tr1
end
