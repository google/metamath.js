include "wo.mm"
include "wleror.mm"
include "ax-a2.mm"
include "bi1.mm"
include "wle3tr1.mm"
include "wletr.mm"

theorem wle2or
  param wva: term a
  param wvb: term b
  param wvc: term c
  param wvd: term d
  assume wle2.1: |- ( a =<2 b ) = 1
  assume wle2.2: |- ( c =<2 d ) = 1


  assert |- ( ( a v c ) =<2 ( b v d ) ) = 1

  proof
    wva
    wvc
    wo
    wvb
    wvc
    wo
    #
    wvb
    wvd
    wo
    #
    wva
    wvb
    wvc
    wle2.1
    wleror
    wvc
    wvb
    wo
    #
    wvd
    wvb
    wo
    #
    @0
    @1
    wvc
    wvd
    wvb
    wle2.2
    wleror
    @0
    @2
    wvb
    wvc
    ax-a2
    bi1
    @1
    @3
    wvb
    wvd
    ax-a2
    bi1
    wle3tr1
    wletr
end
