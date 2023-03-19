include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi1.mm"
include "anass.mm"
include "ax-r1.mm"
include "anidm.mm"
include "ran.mm"
include "ax-r2.mm"
include "lor.mm"
include "df-i1.mm"
include "3tr1.mm"

theorem nom11
  param wva: term a
  param wvb: term b


  assert |- ( a ->1 ( a ^ b ) ) = ( a ->1 b )

  proof
    wva
    wn
    #
    wva
    wva
    wvb
    wa
    #
    wa
    #
    wo
    @0
    @1
    wo
    wva
    @1
    wi1
    wva
    wvb
    wi1
    @2
    @1
    @0
    @2
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @1
    @4
    @2
    wva
    wva
    wvb
    anass
    ax-r1
    @3
    wva
    wvb
    wva
    anidm
    ran
    ax-r2
    lor
    wva
    @1
    df-i1
    wva
    wvb
    df-i1
    3tr1
end
