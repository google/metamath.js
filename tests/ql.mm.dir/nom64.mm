include "wo.mm"
include "wid4.mm"
include "wid1.mm"
include "wi2.mm"
include "nomb41.mm"
include "nom51.mm"
include "ax-r2.mm"

theorem nom64
  let wva: term a
  let wvb: term b


  assert |- ( b ==4 ( a v b ) ) = ( a ->2 b )

  proof
    wvb
    wva
    wvb
    wo
    #
    wid4
    @0
    wvb
    wid1
    wva
    wvb
    wi2
    wvb
    @0
    nomb41
    wva
    wvb
    nom51
    ax-r2
end
