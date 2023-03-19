include "wi2.mm"
include "wa.mm"
include "wt.mm"
include "wn.mm"
include "wi1.mm"
include "wo.mm"
include "le1.mm"
include "ax-r1.mm"
include "lbtr.mm"

theorem womle2b
  let wva: term a
  let wvb: term b
  assume womle2b.1: |- ( ( a ->2 b ) ' v ( a ->1 b ) ) = 1


  assert |- ( a ^ ( a ->2 b ) ) =< ( ( a ->2 b ) ' v ( a ->1 b ) )

  proof
    wva
    wva
    wvb
    wi2
    #
    wa
    #
    wt
    @0
    wn
    wva
    wvb
    wi1
    wo
    #
    @1
    le1
    @2
    wt
    womle2b.1
    ax-r1
    lbtr
end
