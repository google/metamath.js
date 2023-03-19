include "wo.mm"
include "or12.mm"
include "lor.mm"
include "ax-a3.mm"
include "3tr1.mm"

theorem or4
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d


  assert |- ( ( a v b ) v ( c v d ) ) = ( ( a v c ) v ( b v d ) )

  proof
    wva
    wvb
    wvc
    wvd
    wo
    #
    wo
    #
    wo
    wva
    wvc
    wvb
    wvd
    wo
    #
    wo
    #
    wo
    wva
    wvb
    wo
    @0
    wo
    wva
    wvc
    wo
    @2
    wo
    @1
    @3
    wva
    wvb
    wvc
    wvd
    or12
    lor
    wva
    wvb
    @0
    ax-a3
    wva
    wvc
    @2
    ax-a3
    3tr1
end
