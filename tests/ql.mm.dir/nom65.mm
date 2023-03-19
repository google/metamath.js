include "wo.mm"
include "tb.mm"
include "wi2.mm"
include "bicom.mm"
include "nom55.mm"
include "ax-r2.mm"

theorem nom65
  let wva: term a
  let wvb: term b


  assert |- ( b == ( a v b ) ) = ( a ->2 b )

  proof
    wvb
    wva
    wvb
    wo
    #
    tb
    @0
    wvb
    tb
    wva
    wvb
    wi2
    wvb
    @0
    bicom
    wva
    wvb
    nom55
    ax-r2
end
