include "wn.mm"
include "wo.mm"
include "wi2.mm"
include "wi1.mm"
include "wa.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "ud2lem0a.mm"
include "ax-r1.mm"
include "nom12.mm"
include "i1i2.mm"
include "i2i1.mm"
include "3tr1.mm"

theorem nom41
  param wva: term a
  param wvb: term b


  assert |- ( ( a v b ) ->1 b ) = ( a ->2 b )

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
    wi2
    #
    @0
    wva
    wn
    #
    wi1
    #
    @1
    wvb
    wi1
    wva
    wvb
    wi2
    @3
    @0
    @0
    @4
    wa
    #
    wi2
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
    ud2lem0a
    ax-r1
    @0
    @4
    nom12
    ax-r2
    @1
    wvb
    i1i2
    wva
    wvb
    i2i1
    3tr1
end
