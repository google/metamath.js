include "wo.mm"
include "wi2.mm"
include "wn.mm"
include "wa.mm"
include "wt.mm"
include "df-i2.mm"
include "ax-r1.mm"
include "anandir.mm"
include "anass.mm"
include "anor3.mm"
include "lan.mm"
include "ax-r2.mm"
include "2an.mm"
include "3tr2.mm"
include "lor.mm"
include "wi1.mm"
include "df-i1.mm"
include "tb.mm"
include "wlem1.mm"
include "skr0.mm"
include "lea.mm"
include "bltr.mm"
include "le1.mm"
include "lebi.mm"
include "leo.mm"
include "lelan.mm"
include "lelor.mm"
include "2vwomr1a.mm"
include "lear.mm"
include "2vwomlem.mm"

theorem wr5-2v
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume wr5-2v.1: |- ( a == b ) = 1


  assert |- ( ( a v c ) == ( b v c ) ) = 1

  proof
    wva
    wvc
    wo
    #
    wvb
    wvc
    wo
    #
    @0
    @1
    wi2
    @1
    @0
    wn
    #
    @1
    wn
    #
    wa
    #
    wo
    #
    wt
    @0
    @1
    df-i2
    @1
    wva
    wn
    #
    @3
    wa
    #
    wo
    #
    wva
    @1
    wi2
    #
    @5
    wt
    @9
    @8
    wva
    @1
    df-i2
    ax-r1
    @7
    @4
    @1
    @6
    wvb
    wn
    #
    wa
    wvc
    wn
    #
    wa
    #
    @6
    @11
    wa
    #
    @10
    @11
    wa
    #
    wa
    @7
    @4
    @6
    @10
    @11
    anandir
    @12
    @6
    @14
    wa
    @7
    @6
    @10
    @11
    anass
    @14
    @3
    @6
    wvb
    wvc
    anor3
    #
    lan
    ax-r2
    @13
    @2
    @14
    @3
    wva
    wvc
    anor3
    #
    @15
    2an
    3tr2
    lor
    wva
    @1
    wva
    @1
    wi1
    @6
    wva
    @1
    wa
    #
    wo
    #
    wt
    wva
    @1
    df-i1
    wt
    @18
    wt
    @18
    wt
    @6
    wva
    wvb
    wa
    #
    wo
    #
    @18
    wt
    wva
    wvb
    wi1
    #
    @20
    wt
    @21
    wt
    @21
    wvb
    wva
    wi1
    #
    wa
    #
    @21
    @23
    wt
    wva
    wvb
    tb
    @23
    wr5-2v.1
    wva
    wvb
    wlem1
    skr0
    ax-r1
    #
    @21
    @22
    lea
    bltr
    @21
    le1
    lebi
    wva
    wvb
    df-i1
    ax-r2
    @19
    @17
    @6
    wvb
    @1
    wva
    wvb
    wvc
    leo
    lelan
    lelor
    bltr
    @18
    le1
    lebi
    ax-r1
    ax-r2
    2vwomr1a
    3tr2
    ax-r2
    @1
    @0
    wi2
    @0
    @3
    @2
    wa
    #
    wo
    #
    wt
    @1
    @0
    df-i2
    @0
    @10
    @2
    wa
    #
    wo
    #
    wvb
    @0
    wi2
    #
    @26
    wt
    @29
    @28
    wvb
    @0
    df-i2
    ax-r1
    @27
    @25
    @0
    @10
    @6
    wa
    @11
    wa
    #
    @14
    @13
    wa
    @27
    @25
    @10
    @6
    @11
    anandir
    @30
    @10
    @13
    wa
    @27
    @10
    @6
    @11
    anass
    @13
    @2
    @10
    @16
    lan
    ax-r2
    @14
    @3
    @13
    @2
    @15
    @16
    2an
    3tr2
    lor
    wvb
    @0
    wvb
    @0
    wi1
    @10
    wvb
    @0
    wa
    #
    wo
    #
    wt
    wvb
    @0
    df-i1
    wt
    @32
    wt
    @32
    wt
    @10
    wvb
    wva
    wa
    #
    wo
    #
    @32
    wt
    @22
    @34
    wt
    @22
    wt
    @23
    @22
    @24
    @21
    @22
    lear
    bltr
    @22
    le1
    lebi
    wvb
    wva
    df-i1
    ax-r2
    @33
    @31
    @10
    wva
    @0
    wvb
    wva
    wvc
    leo
    lelan
    lelor
    bltr
    @32
    le1
    lebi
    ax-r1
    ax-r2
    2vwomr1a
    3tr2
    ax-r2
    2vwomlem
end
