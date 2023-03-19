include "wo.mm"
include "orordir.mm"
include "ax-r1.mm"
include "df-le2.mm"
include "ax-r5.mm"
include "ax-r2.mm"
include "df-le1.mm"

theorem leror
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume le.1: |- a =< b


  assert |- ( a v c ) =< ( b v c )

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
    wo
    #
    wva
    wvb
    wo
    #
    wvc
    wo
    #
    @1
    @4
    @2
    wva
    wvb
    wvc
    orordir
    ax-r1
    @3
    wvb
    wvc
    wva
    wvb
    le.1
    df-le2
    ax-r5
    ax-r2
    df-le1
end
