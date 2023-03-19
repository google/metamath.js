include "wi2.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-i2.mm"
include "oran.mm"
include "ax-r1.mm"
include "lan.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "con2.mm"

theorem ud2lem0c
  let wva: term a
  let wvb: term b


  assert |- ( a ->2 b ) ' = ( b ' ^ ( a v b ) )

  proof
    wva
    wvb
    wi2
    #
    wvb
    wn
    #
    wva
    wvb
    wo
    #
    wa
    #
    @0
    wvb
    wva
    wn
    @1
    wa
    #
    wo
    #
    @3
    wn
    #
    wva
    wvb
    df-i2
    @5
    @1
    @4
    wn
    #
    wa
    #
    wn
    @6
    wvb
    @4
    oran
    @8
    @3
    @7
    @2
    @1
    @2
    @7
    wva
    wvb
    oran
    ax-r1
    lan
    ax-r4
    ax-r2
    ax-r2
    con2
end
