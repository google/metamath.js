include "wo.mm"
include "orordir.mm"
include "bi1.mm"
include "wr1.mm"
include "wdf-le2.mm"
include "wr5-2v.mm"
include "wr2.mm"
include "wdf-le1.mm"

theorem wleror
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume wle.1: |- ( a =<2 b ) = 1


  assert |- ( ( a v c ) =<2 ( b v c ) ) = 1

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
    @4
    @2
    wva
    wvb
    wvc
    orordir
    bi1
    wr1
    @3
    wvb
    wvc
    wva
    wvb
    wle.1
    wdf-le2
    wr5-2v
    wr2
    wdf-le1
end
