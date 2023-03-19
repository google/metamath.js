include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi3.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "ler2an.mm"
include "ler.mm"
include "i3n1.mm"
include "lan.mm"
include "comor1.mm"
include "comor2.mm"
include "comcom2.mm"
include "com2an.mm"
include "com2or.mm"
include "fh1.mm"
include "ax-r2.mm"
include "ax-r1.mm"
include "lbtr.mm"
include "i3orlem6.mm"

theorem i3orlem7
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( a ^ b ' ) =< ( ( a ->3 b ) ' v ( ( a v c ) ->3 ( b v c ) ) )

  proof
    wva
    wvb
    wn
    #
    wa
    #
    wva
    wvb
    wo
    #
    wva
    wn
    #
    @0
    wi3
    #
    wa
    #
    wva
    wvc
    wo
    wvb
    wvc
    wo
    wi3
    #
    wo
    #
    wva
    wvb
    wi3
    wn
    @6
    wo
    #
    @1
    @5
    @6
    @1
    @2
    @1
    wva
    wvb
    wa
    #
    wo
    #
    wa
    #
    @2
    @3
    wva
    @0
    wo
    #
    wa
    #
    wa
    #
    wo
    #
    @5
    @1
    @11
    @14
    @1
    @2
    @10
    @1
    wva
    @2
    wva
    @0
    lea
    wva
    wvb
    leo
    letr
    @1
    @9
    leo
    ler2an
    ler
    @5
    @15
    @5
    @2
    @10
    @13
    wo
    #
    wa
    @15
    @4
    @16
    @2
    wva
    wvb
    i3n1
    lan
    @2
    @10
    @13
    @2
    @1
    @9
    @2
    wva
    @0
    wva
    wvb
    comor1
    #
    @2
    wvb
    wva
    wvb
    comor2
    #
    comcom2
    #
    com2an
    @2
    wva
    wvb
    @17
    @18
    com2an
    com2or
    @2
    @3
    @12
    @2
    wva
    @17
    comcom2
    @2
    wva
    @0
    @17
    @19
    com2or
    com2an
    fh1
    ax-r2
    ax-r1
    lbtr
    ler
    @8
    @7
    wva
    wvb
    wvc
    i3orlem6
    ax-r1
    lbtr
end
