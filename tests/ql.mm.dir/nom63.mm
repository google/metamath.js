include "wo.mm"
include "wid3.mm"
include "wid2.mm"
include "wi2.mm"
include "nomb32.mm"
include "nom52.mm"
include "ax-r2.mm"

theorem nom63
  param wva: term a
  param wvb: term b


  assert |- ( b ==3 ( a v b ) ) = ( a ->2 b )

  proof
    wvb
    wva
    wvb
    wo
    #
    wid3
    @0
    wvb
    wid2
    wva
    wvb
    wi2
    wvb
    @0
    nomb32
    wva
    wvb
    nom52
    ax-r2
end
