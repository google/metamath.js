include "wa.mm"
include "tb.mm"
include "wi1.mm"
include "bicom.mm"
include "nom25.mm"
include "ax-r2.mm"

theorem nom35
  let wva: term a
  let wvb: term b


  assert |- ( ( a ^ b ) == a ) = ( a ->1 b )

  proof
    wva
    wvb
    wa
    #
    wva
    tb
    wva
    @0
    tb
    wva
    wvb
    wi1
    @0
    wva
    bicom
    wva
    wvb
    nom25
    ax-r2
end
