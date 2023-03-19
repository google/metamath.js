include "wo.mm"
include "wa.mm"
include "tb.mm"
include "wt.mm"
include "bicom.mm"
include "ledi.mm"
include "wn.mm"
include "wf.mm"
include "oran.mm"
include "df-a.mm"
include "con2.mm"
include "ran.mm"
include "ax-r4.mm"
include "ax-r2.mm"
include "lan.mm"
include "an4.mm"
include "ax-a1.mm"
include "ax-r1.mm"
include "bctr.mm"
include "wwcom3ii.mm"
include "ancom.mm"
include "ax-r5.mm"
include "comcom2.mm"
include "anass.mm"
include "an12.mm"
include "dff.mm"
include "3tr1.mm"
include "an0.mm"
include "wwoml3.mm"

theorem wwfh2
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wwfh2.1: |- a C b
  assume wwfh2.2: |- c ' C a


  assert |- ( ( b ^ ( a v c ) ) == ( ( b ^ a ) v ( b ^ c ) ) ) = 1

  proof
    wvb
    wva
    wvc
    wo
    #
    wa
    #
    wvb
    wva
    wa
    #
    wvb
    wvc
    wa
    #
    wo
    #
    tb
    @4
    @1
    tb
    wt
    @1
    @4
    bicom
    @4
    @1
    wvb
    wva
    wvc
    ledi
    @1
    @4
    wn
    #
    wa
    #
    wva
    wn
    #
    wvc
    wvb
    @3
    wn
    #
    wa
    #
    wa
    #
    wa
    #
    wf
    @6
    @7
    wvc
    wa
    #
    @9
    wa
    #
    @11
    @6
    @7
    @0
    wa
    #
    @9
    wa
    #
    @13
    @6
    @7
    wvb
    wa
    #
    @0
    @8
    wa
    #
    wa
    #
    @15
    @6
    @1
    wvb
    wn
    @7
    wo
    #
    @8
    wa
    #
    wa
    #
    @18
    @5
    @20
    @1
    @4
    @20
    @4
    @2
    wn
    #
    @8
    wa
    #
    wn
    @20
    wn
    @2
    @3
    oran
    @23
    @20
    @22
    @19
    @8
    @2
    @19
    wvb
    wva
    df-a
    con2
    ran
    ax-r4
    ax-r2
    con2
    lan
    @21
    wvb
    @19
    wa
    #
    @17
    wa
    @18
    wvb
    @0
    @19
    @8
    an4
    @24
    @16
    @17
    @24
    wvb
    @7
    wa
    @16
    wvb
    @7
    @7
    wn
    #
    wva
    wvb
    wva
    @25
    wva
    ax-a1
    #
    ax-r1
    wwfh2.1
    bctr
    wwcom3ii
    wvb
    @7
    ancom
    ax-r2
    ran
    ax-r2
    ax-r2
    @7
    wvb
    @0
    @8
    an4
    ax-r2
    @14
    @12
    @9
    @14
    @7
    @25
    wvc
    wo
    #
    wa
    @12
    @0
    @27
    @7
    wva
    @25
    wvc
    @26
    ax-r5
    lan
    @7
    wvc
    wvc
    wn
    wva
    wwfh2.2
    comcom2
    wwcom3ii
    ax-r2
    ran
    ax-r2
    @7
    wvc
    @9
    anass
    ax-r2
    @11
    @7
    wf
    wa
    wf
    @10
    wf
    @7
    wvb
    wvc
    @8
    wa
    wa
    #
    @3
    @8
    wa
    #
    @10
    wf
    @29
    @28
    wvb
    wvc
    @8
    anass
    ax-r1
    wvc
    wvb
    @8
    an12
    @3
    dff
    3tr1
    lan
    @7
    an0
    ax-r2
    ax-r2
    wwoml3
    ax-r2
end
