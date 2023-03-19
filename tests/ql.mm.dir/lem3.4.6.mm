include "wo.mm"
include "wi2.mm"
include "wt.mm"
include "lem3.3.6.mm"
include "ax-r1.mm"
include "lem3.4.5.mm"
include "ax-r2.mm"
include "wid5.mm"
include "wa.mm"
include "wn.mm"
include "df-id5.mm"
include "ancom.mm"
include "2or.mm"
include "3tr.mm"
include "lem3.4.4.mm"

theorem lem3.4.6
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume lem3.4.6.1: |- ( a ==5 b ) = 1


  assert |- ( ( a v c ) ==5 ( b v c ) ) = 1

  proof
    wva
    wvc
    wo
    #
    wvb
    wvc
    wo
    #
    @0
    @1
    wi2
    #
    wva
    @1
    wi2
    #
    wt
    @3
    @2
    wva
    wvb
    wvc
    lem3.3.6
    ax-r1
    wva
    wvb
    wvc
    lem3.4.6.1
    lem3.4.5
    ax-r2
    @1
    @0
    wi2
    #
    wvb
    @0
    wi2
    #
    wt
    @5
    @4
    wvb
    wva
    wvc
    lem3.3.6
    ax-r1
    wvb
    wva
    wvc
    wvb
    wva
    wid5
    wvb
    wva
    wa
    #
    wvb
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
    wvb
    wva
    df-id5
    @10
    wva
    wvb
    wa
    #
    @8
    @7
    wa
    #
    wo
    #
    wva
    wvb
    wid5
    #
    wt
    @6
    @11
    @9
    @12
    wvb
    wva
    ancom
    @7
    @8
    ancom
    2or
    @14
    @13
    wva
    wvb
    df-id5
    ax-r1
    lem3.4.6.1
    3tr
    ax-r2
    lem3.4.5
    ax-r2
    lem3.4.4
end
