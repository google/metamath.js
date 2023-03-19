include "wn.mm"
include "wa.mm"
include "tb.mm"
include "wi1.mm"
include "wo.mm"
include "wi2.mm"
include "nom25.mm"
include "conb.mm"
include "bicom.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "lbi.mm"
include "3tr.mm"
include "i2i1.mm"
include "3tr1.mm"

theorem nom55
  let wva: term a
  let wvb: term b


  assert |- ( ( a v b ) == b ) = ( a ->2 b )

  proof
    wvb
    wn
    #
    @0
    wva
    wn
    #
    wa
    #
    tb
    #
    @0
    @1
    wi1
    wva
    wvb
    wo
    #
    wvb
    tb
    #
    wva
    wvb
    wi2
    @0
    @1
    nom25
    @5
    @4
    wn
    #
    @0
    tb
    @0
    @6
    tb
    @3
    @4
    wvb
    conb
    @6
    @0
    bicom
    @6
    @2
    @0
    @2
    @6
    @2
    @1
    @0
    wa
    @6
    @0
    @1
    ancom
    wva
    wvb
    anor3
    ax-r2
    ax-r1
    lbi
    3tr
    wva
    wvb
    i2i1
    3tr1
end
