include "wo.mm"
include "ax-a2.mm"
include "lor.mm"
include "or4.mm"
include "ax-r2.mm"

theorem or42
  let wva: term a
  let wvb: term b
  let wvc: term c
  let wvd: term d


  assert |- ( ( a v b ) v ( c v d ) ) = ( ( a v d ) v ( b v c ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wvd
    wo
    #
    wo
    @0
    wvd
    wvc
    wo
    #
    wo
    wva
    wvd
    wo
    wvb
    wvc
    wo
    wo
    @1
    @2
    @0
    wvc
    wvd
    ax-a2
    lor
    wva
    wvb
    wvd
    wvc
    or4
    ax-r2
end
