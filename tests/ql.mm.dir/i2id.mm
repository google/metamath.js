include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wt.mm"
include "df-i2.mm"
include "anidm.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem i2id
  let wva: term a


  assert |- ( a ->2 a ) = 1

  proof
    wva
    wva
    wi2
    wva
    wva
    wn
    #
    @0
    wa
    #
    wo
    #
    wt
    wva
    wva
    df-i2
    @2
    wva
    @0
    wo
    #
    wt
    @1
    @0
    wva
    @0
    anidm
    lor
    wt
    @3
    wva
    df-t
    ax-r1
    ax-r2
    ax-r2
end
