include "wn.mm"
include "ax-a1.mm"
include "ax-r1.mm"
include "ax-r2.mm"

theorem id
  let wva: term a


  assert |- a = a

  proof
    wva
    wva
    wn
    wn
    #
    wva
    wva
    ax-a1
    #
    wva
    @0
    @1
    ax-r1
    ax-r2
end
