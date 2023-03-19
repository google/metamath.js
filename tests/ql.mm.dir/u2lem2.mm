include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i2.mm"
include "u2lem1n.mm"
include "ran.mm"
include "anidm.mm"
include "ax-r2.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r1.mm"

theorem u2lem2
  let wva: term a
  let wvb: term b


  assert |- ( ( ( a ->2 b ) ->2 a ) ->2 a ) = 1

  proof
    wva
    wvb
    wi2
    wva
    wi2
    #
    wva
    wi2
    wva
    @0
    wn
    #
    wva
    wn
    #
    wa
    #
    wo
    #
    wt
    @0
    wva
    df-i2
    @4
    wva
    @2
    wo
    #
    wt
    @3
    @2
    wva
    @3
    @2
    @2
    wa
    @2
    @1
    @2
    @2
    wva
    wvb
    u2lem1n
    ran
    @2
    anidm
    ax-r2
    lor
    wt
    @5
    wva
    df-t
    ax-r1
    ax-r2
    ax-r2
end
