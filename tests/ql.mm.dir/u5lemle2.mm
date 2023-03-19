include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "wi5.mm"
include "df-i5.mm"
include "ax-r1.mm"
include "ax-r2.mm"
include "lan.mm"
include "comanr1.mm"
include "comcom6.mm"
include "com2or.mm"
include "fh1.mm"
include "wf.mm"
include "anass.mm"
include "anidm.mm"
include "ran.mm"
include "ancom.mm"
include "dff.mm"
include "an0.mm"
include "3tr2.mm"
include "2or.mm"
include "or0.mm"
include "an1.mm"
include "df2le1.mm"

theorem u5lemle2
  param wva: term a
  param wvb: term b
  assume u5lemle2.1: |- ( a ->5 b ) = 1


  assert |- a =< b

  proof
    wva
    wvb
    wva
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wa
    #
    wo
    #
    @1
    wvb
    wn
    #
    wa
    #
    wo
    #
    wa
    #
    wva
    wt
    wa
    @0
    wva
    @6
    wt
    wva
    @6
    wva
    wvb
    wi5
    #
    wt
    @8
    @6
    wva
    wvb
    df-i5
    ax-r1
    u5lemle2.1
    ax-r2
    lan
    @7
    wva
    @3
    wa
    #
    wva
    @5
    wa
    #
    wo
    #
    @0
    wva
    @3
    @5
    wva
    @0
    @2
    wva
    wvb
    comanr1
    #
    wva
    @2
    @1
    wvb
    comanr1
    comcom6
    #
    com2or
    wva
    @5
    @1
    @4
    comanr1
    comcom6
    fh1
    @11
    @0
    wf
    wo
    #
    @0
    @9
    @0
    @10
    wf
    @9
    wva
    @0
    wa
    #
    wva
    @2
    wa
    #
    wo
    #
    @0
    wva
    @0
    @2
    @12
    @13
    fh1
    @17
    @14
    @0
    @15
    @0
    @16
    wf
    @15
    wva
    wva
    wa
    #
    wvb
    wa
    #
    @0
    @19
    @15
    wva
    wva
    wvb
    anass
    ax-r1
    @18
    wva
    wvb
    wva
    anidm
    ran
    ax-r2
    wva
    @1
    wa
    #
    wvb
    wa
    wvb
    @20
    wa
    #
    @16
    wf
    @20
    wvb
    ancom
    wva
    @1
    wvb
    anass
    @21
    wvb
    wf
    wa
    wf
    @20
    wf
    wvb
    wf
    @20
    wva
    dff
    #
    ax-r1
    lan
    wvb
    an0
    ax-r2
    3tr2
    2or
    @0
    or0
    #
    ax-r2
    ax-r2
    @20
    @4
    wa
    @4
    @20
    wa
    #
    @10
    wf
    @20
    @4
    ancom
    wva
    @1
    @4
    anass
    @24
    @4
    wf
    wa
    #
    wf
    @25
    @24
    wf
    @20
    @4
    @22
    lan
    ax-r1
    @4
    an0
    ax-r2
    3tr2
    2or
    @23
    ax-r2
    ax-r2
    wva
    an1
    3tr2
    df2le1
end
