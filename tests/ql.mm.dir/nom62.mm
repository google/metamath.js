include "wo.mm"
include "wid2.mm"
include "wid3.mm"
include "wi2.mm"
include "nomb32.mm"
include "ax-r1.mm"
include "nom53.mm"
include "ax-r2.mm"

theorem nom62
  param wva: term a
  param wvb: term b


  assert |- ( b ==2 ( a v b ) ) = ( a ->2 b )

  proof
    wvb
    wva
    wvb
    wo
    #
    wid2
    #
    @0
    wvb
    wid3
    #
    wva
    wvb
    wi2
    @2
    @1
    @0
    wvb
    nomb32
    ax-r1
    wva
    wvb
    nom53
    ax-r2
end
