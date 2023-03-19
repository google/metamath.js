include "wi2.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "df-a.mm"
include "ax-r1.mm"
include "u2lemab.mm"
include "ax-r2.mm"
include "con3.mm"

theorem u2lemnonb
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->2 b ) ' v b ' ) = b '

  proof
    wva
    wvb
    wi2
    #
    wn
    wvb
    wn
    wo
    #
    wvb
    @1
    wn
    #
    @0
    wvb
    wa
    #
    wvb
    @3
    @2
    @0
    wvb
    df-a
    ax-r1
    wva
    wvb
    u2lemab
    ax-r2
    con3
end
