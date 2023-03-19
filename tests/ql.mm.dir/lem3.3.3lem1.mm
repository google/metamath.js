include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wid5.mm"
include "wi1.mm"
include "ax-a2.mm"
include "lea.mm"
include "leror.mm"
include "bltr.mm"
include "df-id5.mm"
include "df-i1.mm"
include "le3tr1.mm"

theorem lem3.3.3lem1
  let wva: term a
  let wvb: term b


  assert |- ( a ==5 b ) =< ( a ->1 b )

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
    @0
    wo
    #
    wva
    wvb
    wid5
    wva
    wvb
    wi1
    @4
    @3
    @0
    wo
    @5
    @0
    @3
    ax-a2
    @3
    @1
    @0
    @1
    @2
    lea
    leror
    bltr
    wva
    wvb
    df-id5
    wva
    wvb
    df-i1
    le3tr1
end
