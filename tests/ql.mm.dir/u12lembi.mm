include "wi1.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi2.mm"
include "tb.mm"
include "u1lemc1.mm"
include "comcom.mm"
include "lear.mm"
include "leo.mm"
include "df-i1.mm"
include "ax-r1.mm"
include "lbtr.mm"
include "letr.mm"
include "lecom.mm"
include "fh1.mm"
include "u1lemaa.mm"
include "an12.mm"
include "u1lemana.mm"
include "lan.mm"
include "ancom.mm"
include "3tr.mm"
include "2or.mm"
include "ax-r2.mm"
include "df-i2.mm"
include "dfb.mm"
include "3tr1.mm"

theorem u12lembi
  let wva: term a
  let wvb: term b


  assert |- ( ( a ->1 b ) ^ ( b ->2 a ) ) = ( a == b )

  proof
    wva
    wvb
    wi1
    #
    wva
    wvb
    wn
    #
    wva
    wn
    #
    wa
    #
    wo
    #
    wa
    #
    wva
    wvb
    wa
    #
    @2
    @1
    wa
    #
    wo
    #
    @0
    wvb
    wva
    wi2
    #
    wa
    wva
    wvb
    tb
    @5
    @0
    wva
    wa
    #
    @0
    @3
    wa
    #
    wo
    @8
    @0
    wva
    @3
    wva
    @0
    wva
    wvb
    u1lemc1
    comcom
    @3
    @0
    @3
    @0
    @3
    @2
    @0
    @1
    @2
    lear
    @2
    @2
    @6
    wo
    #
    @0
    @2
    @6
    leo
    @0
    @12
    wva
    wvb
    df-i1
    ax-r1
    lbtr
    letr
    lecom
    comcom
    fh1
    @10
    @6
    @11
    @7
    wva
    wvb
    u1lemaa
    @11
    @1
    @0
    @2
    wa
    #
    wa
    @3
    @7
    @0
    @1
    @2
    an12
    @13
    @2
    @1
    wva
    wvb
    u1lemana
    lan
    @1
    @2
    ancom
    3tr
    2or
    ax-r2
    @9
    @4
    @0
    wvb
    wva
    df-i2
    lan
    wva
    wvb
    dfb
    3tr1
end
