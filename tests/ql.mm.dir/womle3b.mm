include "wi1.mm"
include "wa.mm"
include "wt.mm"
include "wn.mm"
include "wi2.mm"
include "wo.mm"
include "le1.mm"
include "ax-r1.mm"
include "lbtr.mm"

theorem womle3b
  param wva: term a
  param wvb: term b
  assume womle3b.1: |- ( ( a ->1 b ) ' v ( a ->2 b ) ) = 1


  assert |- ( a ^ ( a ->1 b ) ) =< ( ( a ->1 b ) ' v ( a ->2 b ) )

  proof
    wva
    wva
    wvb
    wi1
    #
    wa
    #
    wt
    @0
    wn
    wva
    wvb
    wi2
    wo
    #
    @1
    le1
    @2
    wt
    womle3b.1
    ax-r1
    lbtr
end
