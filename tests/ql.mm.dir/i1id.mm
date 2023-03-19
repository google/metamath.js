include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i1.mm"
include "ax-a2.mm"
include "anidm.mm"
include "lor.mm"
include "df-t.mm"
include "3tr1.mm"
include "ax-r2.mm"

theorem i1id
  param wva: term a


  assert |- ( a ->1 a ) = 1

  proof
    wva
    wva
    wi1
    wva
    wn
    #
    wva
    wva
    wa
    #
    wo
    #
    wt
    wva
    wva
    df-i1
    @0
    wva
    wo
    wva
    @0
    wo
    @2
    wt
    @0
    wva
    ax-a2
    @1
    wva
    @0
    wva
    anidm
    lor
    wva
    df-t
    3tr1
    ax-r2
end
