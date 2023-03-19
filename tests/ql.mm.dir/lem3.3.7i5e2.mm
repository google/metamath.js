include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wid5.mm"
include "ancom.mm"
include "2or.mm"
include "ax-r1.mm"
include "df-id5.mm"
include "3tr1.mm"

theorem lem3.3.7i5e2
  let wva: term a
  let wvb: term b


  assert |- ( a ==5 ( a ^ b ) ) = ( ( a ^ b ) ==5 a )

  proof
    wva
    wva
    wvb
    wa
    #
    wa
    #
    wva
    wn
    #
    @0
    wn
    #
    wa
    #
    wo
    #
    @0
    wva
    wa
    #
    @3
    @2
    wa
    #
    wo
    #
    wva
    @0
    wid5
    @0
    wva
    wid5
    @8
    @5
    @6
    @1
    @7
    @4
    @0
    wva
    ancom
    @3
    @2
    ancom
    2or
    ax-r1
    wva
    @0
    df-id5
    @0
    wva
    df-id5
    3tr1
end
