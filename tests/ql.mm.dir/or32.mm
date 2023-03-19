include "wo.mm"
include "ax-a2.mm"
include "lor.mm"
include "ax-a3.mm"
include "3tr1.mm"

theorem or32
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( a v b ) v c ) = ( ( a v c ) v b )

  proof
    wva
    wvb
    wvc
    wo
    #
    wo
    wva
    wvc
    wvb
    wo
    #
    wo
    wva
    wvb
    wo
    wvc
    wo
    wva
    wvc
    wo
    wvb
    wo
    @0
    @1
    wva
    wvb
    wvc
    ax-a2
    lor
    wva
    wvb
    wvc
    ax-a3
    wva
    wvc
    wvb
    ax-a3
    3tr1
end
