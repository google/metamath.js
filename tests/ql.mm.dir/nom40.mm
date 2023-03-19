include "wn.mm"
include "wa.mm"
include "wi0.mm"
include "wi1.mm"
include "wo.mm"
include "wi2.mm"
include "nom10.mm"
include "ax-a2.mm"
include "ax-a1.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "2or.mm"
include "df-i0.mm"
include "3tr1.mm"
include "i2i1.mm"

theorem nom40
  let wva: term a
  let wvb: term b


  assert |- ( ( a v b ) ->0 b ) = ( a ->2 b )

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
    wi0
    #
    @0
    @1
    wi1
    wva
    wvb
    wo
    #
    wvb
    wi0
    #
    wva
    wvb
    wi2
    @0
    @1
    nom10
    @4
    wn
    #
    wvb
    wo
    #
    @0
    wn
    #
    @2
    wo
    #
    @5
    @3
    @7
    wvb
    @6
    wo
    @9
    @6
    wvb
    ax-a2
    wvb
    @8
    @6
    @2
    wvb
    ax-a1
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
    2or
    ax-r2
    @4
    wvb
    df-i0
    @0
    @2
    df-i0
    3tr1
    wva
    wvb
    i2i1
    3tr1
end
