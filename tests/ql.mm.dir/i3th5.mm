include "wi3.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "ax-a2.mm"
include "lea.mm"
include "lear.mm"
include "le2or.mm"
include "bltr.mm"
include "oridm.mm"
include "lbtr.mm"
include "df-i3.mm"
include "lem4.mm"
include "le3tr1.mm"
include "lei3.mm"

theorem i3th5
  param wva: term a
  param wvb: term b


  assert |- ( ( a ->3 b ) ->3 ( a ->3 ( a ->3 b ) ) ) = 1

  proof
    wva
    wvb
    wi3
    #
    wva
    @0
    wi3
    #
    wva
    wn
    #
    wvb
    wa
    #
    @2
    wvb
    wn
    #
    wa
    #
    wo
    #
    wva
    @2
    wvb
    wo
    #
    wa
    #
    wo
    #
    @7
    @0
    @1
    @9
    @7
    @7
    wo
    @7
    @6
    @7
    @8
    @7
    @6
    @5
    @3
    wo
    @7
    @3
    @5
    ax-a2
    @5
    @2
    @3
    wvb
    @2
    @4
    lea
    @2
    wvb
    lear
    le2or
    bltr
    wva
    @7
    lear
    le2or
    @7
    oridm
    lbtr
    wva
    wvb
    df-i3
    wva
    wvb
    lem4
    le3tr1
    lei3
end
