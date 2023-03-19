include "wa.mm"
include "wn.mm"
include "wo.mm"
include "tb.mm"
include "wid0.mm"
include "ax-a2.mm"
include "lea.mm"
include "lear.mm"
include "le2or.mm"
include "ler2an.mm"
include "bltr.mm"
include "dfb.mm"
include "df-id0.mm"
include "le3tr1.mm"

theorem id5leid0
  let wva: term a
  let wvb: term b


  assert |- ( a == b ) =< ( a ==0 b )

  proof
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
    @1
    wvb
    wo
    #
    @2
    wva
    wo
    #
    wa
    #
    wva
    wvb
    tb
    wva
    wvb
    wid0
    @4
    @3
    @0
    wo
    #
    @7
    @0
    @3
    ax-a2
    @8
    @5
    @6
    @3
    @1
    @0
    wvb
    @1
    @2
    lea
    wva
    wvb
    lear
    le2or
    @3
    @2
    @0
    wva
    @1
    @2
    lear
    wva
    wvb
    lea
    le2or
    ler2an
    bltr
    wva
    wvb
    dfb
    wva
    wvb
    df-id0
    le3tr1
end
