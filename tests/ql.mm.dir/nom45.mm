include "wn.mm"
include "wo.mm"
include "wi5.mm"
include "wi1.mm"
include "wi2.mm"
include "wa.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "ud5lem0a.mm"
include "ax-r1.mm"
include "nom15.mm"
include "i5con.mm"
include "i2i1.mm"
include "3tr1.mm"

theorem nom45
  param wva: term a
  param wvb: term b


  assert |- ( ( a v b ) ->5 b ) = ( a ->2 b )

  proof
    wvb
    wn
    #
    wva
    wvb
    wo
    #
    wn
    #
    wi5
    #
    @0
    wva
    wn
    #
    wi1
    #
    @1
    wvb
    wi5
    wva
    wvb
    wi2
    @3
    @0
    @0
    @4
    wa
    #
    wi5
    #
    @5
    @7
    @3
    @6
    @2
    @0
    @6
    @4
    @0
    wa
    @2
    @0
    @4
    ancom
    wva
    wvb
    anor3
    ax-r2
    ud5lem0a
    ax-r1
    @0
    @4
    nom15
    ax-r2
    @1
    wvb
    i5con
    wva
    wvb
    i2i1
    3tr1
end
