include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "wi1.mm"
include "ax-a3.mm"
include "ax-a2.mm"
include "ax-r2.mm"
include "lea.mm"
include "lel2or.mm"
include "leror.mm"
include "bltr.mm"
include "df-i5.mm"
include "df-i1.mm"
include "le3tr1.mm"

theorem i5lei1
  let wva: term a
  let wvb: term b


  assert |- ( a ->5 b ) =< ( a ->1 b )

  proof
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    @1
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
    wi5
    wva
    wvb
    wi1
    @5
    @2
    @4
    wo
    #
    @0
    wo
    #
    @6
    @5
    @0
    @7
    wo
    @8
    @0
    @2
    @4
    ax-a3
    @0
    @7
    ax-a2
    ax-r2
    @7
    @1
    @0
    @2
    @1
    @4
    @1
    wvb
    lea
    @1
    @3
    lea
    lel2or
    leror
    bltr
    wva
    wvb
    df-i5
    wva
    wvb
    df-i1
    le3tr1
end
