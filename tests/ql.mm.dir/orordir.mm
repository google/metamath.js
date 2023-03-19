include "wo.mm"
include "oridm.mm"
include "ax-r1.mm"
include "lor.mm"
include "or4.mm"
include "ax-r2.mm"

theorem orordir
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a v b ) v c ) = ( ( a v c ) v ( b v c ) )

  proof
    wva
    wvb
    wo
    #
    wvc
    wo
    @0
    wvc
    wvc
    wo
    #
    wo
    wva
    wvc
    wo
    wvb
    wvc
    wo
    wo
    wvc
    @1
    @0
    @1
    wvc
    wvc
    oridm
    ax-r1
    lor
    wva
    wvb
    wvc
    wvc
    or4
    ax-r2
end
