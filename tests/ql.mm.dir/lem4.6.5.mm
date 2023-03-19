include "wi1.mm"
include "wn.mm"
include "u1lemn1b.mm"
include "ax-r1.mm"

theorem lem4.6.5
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) ' ->1 b ) = ( a ->1 b )

  proof
    wva
    wvb
    wi1
    #
    @0
    wn
    wvb
    wi1
    wva
    wvb
    u1lemn1b
    ax-r1
end
