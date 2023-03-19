include "wa.mm"
include "wid3.mm"
include "wid2.mm"
include "wi1.mm"
include "nomb32.mm"
include "nom22.mm"
include "ax-r2.mm"

theorem nom33
  let wva: term a
  let wvb: term b


  assert |- ( ( a ^ b ) ==3 a ) = ( a ->1 b )

  proof
    wva
    wvb
    wa
    #
    wva
    wid3
    wva
    @0
    wid2
    wva
    wvb
    wi1
    @0
    wva
    nomb32
    wva
    wvb
    nom22
    ax-r2
end
