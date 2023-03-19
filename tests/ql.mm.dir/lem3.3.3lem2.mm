include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wid5.mm"
include "wi1.mm"
include "lear.mm"
include "leror.mm"
include "ax-a2.mm"
include "ancom.mm"
include "lor.mm"
include "le3tr1.mm"
include "df-id5.mm"
include "df-i1.mm"

theorem lem3.3.3lem2
  param wva: term a
  param wvb: term b


  assert |- ( a ==5 b ) =< ( b ->1 a )

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
    @2
    wvb
    wva
    wa
    #
    wo
    #
    wva
    wvb
    wid5
    wvb
    wva
    wi1
    @3
    @0
    wo
    @2
    @0
    wo
    @4
    @6
    @3
    @2
    @0
    @1
    @2
    lear
    leror
    @0
    @3
    ax-a2
    @5
    @0
    @2
    wvb
    wva
    ancom
    lor
    le3tr1
    wva
    wvb
    df-id5
    wvb
    wva
    df-i1
    le3tr1
end
