include "wn.mm"
include "wi1.mm"
include "wi2.mm"
include "i1i2.mm"
include "ax-a1.mm"
include "ax-r1.mm"
include "ud2lem0b.mm"
include "ax-r2.mm"

theorem i1i2con1
  let wva: term a
  let wvb: term b


  assert |- ( a ->1 b ' ) = ( b ->2 a ' )

  proof
    wva
    wvb
    wn
    #
    wi1
    @0
    wn
    #
    wva
    wn
    #
    wi2
    wvb
    @2
    wi2
    wva
    @0
    i1i2
    @1
    wvb
    @2
    wvb
    @1
    wvb
    ax-a1
    ax-r1
    ud2lem0b
    ax-r2
end
