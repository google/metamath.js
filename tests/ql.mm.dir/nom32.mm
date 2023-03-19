include "wa.mm"
include "wid2.mm"
include "wid3.mm"
include "wi1.mm"
include "nomb32.mm"
include "ax-r1.mm"
include "nom23.mm"
include "ax-r2.mm"

theorem nom32
  let wva: term a
  let wvb: term b


  assert |- ( ( a ^ b ) ==2 a ) = ( a ->1 b )

  proof
    wva
    wvb
    wa
    #
    wva
    wid2
    #
    wva
    @0
    wid3
    #
    wva
    wvb
    wi1
    @2
    @1
    wva
    @0
    nomb32
    ax-r1
    wva
    wvb
    nom23
    ax-r2
end
