include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-a.mm"
include "oridm.mm"
include "con2.mm"
include "ax-r2.mm"

theorem anidm
  let wva: term a


  assert |- ( a ^ a ) = a

  proof
    wva
    wva
    wa
    wva
    wn
    #
    @0
    wo
    #
    wn
    wva
    wva
    wva
    df-a
    @1
    wva
    @0
    oridm
    con2
    ax-r2
end
