include "wo.mm"
include "tb.mm"
include "ax-a2.mm"
include "2bi.mm"
include "bi1.mm"

theorem ska2a
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( ( ( a v c ) == ( b v c ) ) == ( ( c v a ) == ( c v b ) ) ) = 1

  proof
    wva
    wvc
    wo
    #
    wvb
    wvc
    wo
    #
    tb
    wvc
    wva
    wo
    #
    wvc
    wvb
    wo
    #
    tb
    @0
    @2
    @1
    @3
    wva
    wvc
    ax-a2
    wvb
    wvc
    ax-a2
    2bi
    bi1
end
