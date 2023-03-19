include "wn.mm"
include "wo.mm"
include "wid0.mm"
include "wi1.mm"
include "wi2.mm"
include "wa.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "lor.mm"
include "ax-r4.mm"
include "ax-r5.mm"
include "2an.mm"
include "ax-r1.mm"
include "df-id0.mm"
include "3tr1.mm"
include "nom20.mm"
include "nomcon0.mm"
include "i2i1.mm"

theorem nom50
  let wva: term a
  let wvb: term b


  assert |- ( ( a v b ) ==0 b ) = ( a ->2 b )

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
    wid0
    #
    @0
    wva
    wn
    #
    wi1
    #
    @1
    wvb
    wid0
    wva
    wvb
    wi2
    @3
    @0
    @0
    @4
    wa
    #
    wid0
    #
    @5
    @0
    wn
    #
    @2
    wo
    #
    @2
    wn
    #
    @0
    wo
    #
    wa
    #
    @8
    @6
    wo
    #
    @6
    wn
    #
    @0
    wo
    #
    wa
    #
    @3
    @7
    @16
    @12
    @13
    @9
    @15
    @11
    @6
    @2
    @8
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
    #
    lor
    @14
    @10
    @0
    @6
    @2
    @17
    ax-r4
    ax-r5
    2an
    ax-r1
    @0
    @2
    df-id0
    @0
    @6
    df-id0
    3tr1
    @0
    @4
    nom20
    ax-r2
    @1
    wvb
    nomcon0
    wva
    wvb
    i2i1
    3tr1
end
