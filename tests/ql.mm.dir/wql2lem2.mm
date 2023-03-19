include "wo.mm"
include "wn.mm"
include "wi2.mm"
include "wt.mm"
include "wa.mm"
include "df-i2.mm"
include "anor3.mm"
include "ax-a3.mm"
include "ax-r1.mm"
include "orordir.mm"
include "ax-r2.mm"
include "ax-r4.mm"
include "lor.mm"
include "ax-a2.mm"
include "3tr.mm"

theorem wql2lem2
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wql2lem2.1: |- ( ( a v c ) ->2 ( b v c ) ) = 1


  assert |- ( ( a v ( b v c ) ) ' v ( b v c ) ) = 1

  proof
    wva
    wvb
    wvc
    wo
    #
    wo
    #
    wn
    #
    @0
    wo
    #
    wva
    wvc
    wo
    #
    @0
    wi2
    #
    wt
    @5
    @3
    @5
    @0
    @4
    wn
    @0
    wn
    wa
    #
    wo
    @0
    @2
    wo
    @3
    @4
    @0
    df-i2
    @6
    @2
    @0
    @6
    @4
    @0
    wo
    #
    wn
    #
    @2
    @4
    @0
    anor3
    @2
    @8
    @1
    @7
    @1
    wva
    wvb
    wo
    wvc
    wo
    #
    @7
    @9
    @1
    wva
    wvb
    wvc
    ax-a3
    ax-r1
    wva
    wvb
    wvc
    orordir
    ax-r2
    ax-r4
    ax-r1
    ax-r2
    lor
    @0
    @2
    ax-a2
    3tr
    ax-r1
    wql2lem2.1
    ax-r2
end
