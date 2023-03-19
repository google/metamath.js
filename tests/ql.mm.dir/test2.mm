include "wo.mm"
include "tb.mm"
include "wn.mm"
include "wa.mm"
include "dfnb.mm"
include "anidm.mm"
include "2or.mm"
include "comor1.mm"
include "comor2.mm"
include "com2an.mm"
include "comcom2.mm"
include "com2or.mm"
include "fh4r.mm"
include "wt.mm"
include "ax-a2.mm"
include "lea.mm"
include "leo.mm"
include "letr.mm"
include "df-le2.mm"
include "ax-r2.mm"
include "df-a.mm"
include "lor.mm"
include "df-t.mm"
include "ax-r1.mm"
include "2an.mm"
include "an1.mm"
include "leor.mm"
include "le2an.mm"
include "lelor.mm"
include "bltr.mm"

theorem test2
  let wva: term a
  let wvb: term b
  let wvc: term c


  assert |- ( a v b ) =< ( ( a == b ) ' v ( ( c v ( a ^ b ) ) ^ ( c ' v ( a ^ b ) ) ) )

  proof
    wva
    wvb
    wo
    #
    wva
    wvb
    tb
    wn
    #
    wva
    wvb
    wa
    #
    @2
    wa
    #
    wo
    #
    @1
    wvc
    @2
    wo
    #
    wvc
    wn
    #
    @2
    wo
    #
    wa
    #
    wo
    @4
    @0
    @4
    @0
    wva
    wn
    #
    wvb
    wn
    #
    wo
    #
    wa
    #
    @2
    wo
    #
    @0
    @1
    @12
    @3
    @2
    wva
    wvb
    dfnb
    @2
    anidm
    2or
    @13
    @0
    @2
    wo
    #
    @11
    @2
    wo
    #
    wa
    #
    @0
    @0
    @2
    @11
    @0
    wva
    wvb
    wva
    wvb
    comor1
    #
    wva
    wvb
    comor2
    #
    com2an
    @0
    @9
    @10
    @0
    wva
    @17
    comcom2
    @0
    wvb
    @18
    comcom2
    com2or
    fh4r
    @16
    @0
    wt
    wa
    @0
    @14
    @0
    @15
    wt
    @14
    @2
    @0
    wo
    @0
    @0
    @2
    ax-a2
    @2
    @0
    @2
    wva
    @0
    wva
    wvb
    lea
    wva
    wvb
    leo
    letr
    df-le2
    ax-r2
    @15
    @11
    @11
    wn
    #
    wo
    #
    wt
    @2
    @19
    @11
    wva
    wvb
    df-a
    lor
    wt
    @20
    @11
    df-t
    ax-r1
    ax-r2
    2an
    @0
    an1
    ax-r2
    ax-r2
    ax-r2
    ax-r1
    @3
    @8
    @1
    @2
    @5
    @2
    @7
    @2
    wvc
    leor
    @2
    @6
    leor
    le2an
    lelor
    bltr
end
