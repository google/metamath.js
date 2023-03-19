include "wid5.mm"
include "wb1.mm"
include "wi0.mm"
include "wn.mm"
include "wo.mm"
include "wi1.mm"
include "wa.mm"
include "wt.mm"
include "df-i0.mm"
include "df-b1.mm"
include "lor.mm"
include "lem3.3.3lem3.mm"
include "sklem.mm"
include "3tr.mm"

theorem lem3.3.3
  param wva: term a
  param wvb: term b


  assert |- ( ( a ==5 b ) ->0 ( a <->1 b ) ) = 1

  proof
    wva
    wvb
    wid5
    #
    wva
    wvb
    wb1
    #
    wi0
    @0
    wn
    #
    @1
    wo
    @2
    wva
    wvb
    wi1
    wvb
    wva
    wi1
    wa
    #
    wo
    wt
    @0
    @1
    df-i0
    @1
    @3
    @2
    wva
    wvb
    df-b1
    lor
    @0
    @3
    wva
    wvb
    lem3.3.3lem3
    sklem
    3tr
end
