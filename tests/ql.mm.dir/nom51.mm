include "wn.mm"
include "wo.mm"
include "wid2.mm"
include "wi1.mm"
include "wid1.mm"
include "wi2.mm"
include "wa.mm"
include "ancom.mm"
include "anor3.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "ax-r4.mm"
include "lor.mm"
include "lan.mm"
include "2or.mm"
include "2an.mm"
include "df-id2.mm"
include "3tr1.mm"
include "nom22.mm"
include "nomcon1.mm"
include "i2i1.mm"

theorem nom51
  param wva: term a
  param wvb: term b


  assert |- ( ( a v b ) ==1 b ) = ( a ->2 b )

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
    wid2
    #
    @0
    wva
    wn
    #
    wi1
    #
    @1
    wvb
    wid1
    wva
    wvb
    wi2
    @3
    @0
    @0
    @4
    wa
    #
    wid2
    #
    @5
    @0
    @2
    wn
    #
    wo
    #
    @2
    @0
    wn
    #
    @8
    wa
    #
    wo
    #
    wa
    @0
    @6
    wn
    #
    wo
    #
    @6
    @10
    @13
    wa
    #
    wo
    #
    wa
    @3
    @7
    @9
    @14
    @12
    @16
    @8
    @13
    @0
    @2
    @6
    @6
    @2
    @6
    @4
    @0
    wa
    #
    @2
    @0
    @4
    ancom
    wva
    wvb
    anor3
    #
    ax-r2
    ax-r1
    #
    ax-r4
    lor
    @2
    @6
    @11
    @15
    @19
    @8
    @13
    @10
    @2
    @6
    @2
    @17
    @6
    @17
    @2
    @18
    ax-r1
    @4
    @0
    ancom
    ax-r2
    ax-r4
    lan
    2or
    2an
    @0
    @2
    df-id2
    @0
    @6
    df-id2
    3tr1
    @0
    @4
    nom22
    ax-r2
    @1
    wvb
    nomcon1
    wva
    wvb
    i2i1
    3tr1
end
