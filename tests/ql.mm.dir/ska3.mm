include "wn.mm"
include "tb.mm"
include "wo.mm"
include "wt.mm"
include "conb.mm"
include "ax-r4.mm"
include "lor.mm"
include "ax-a2.mm"
include "df-t.mm"
include "3tr1.mm"

theorem ska3
  let wva: term a
  let wvb: term b


  assert |- ( ( a == b ) ' v ( a ' == b ' ) ) = 1

  proof
    wva
    wn
    wvb
    wn
    tb
    #
    wva
    wvb
    tb
    #
    wn
    #
    wo
    @0
    @0
    wn
    #
    wo
    @2
    @0
    wo
    wt
    @2
    @3
    @0
    @1
    @0
    wva
    wvb
    conb
    ax-r4
    lor
    @2
    @0
    ax-a2
    @0
    df-t
    3tr1
end
