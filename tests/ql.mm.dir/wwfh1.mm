include "wo.mm"
include "wa.mm"
include "tb.mm"
include "wt.mm"
include "bicom.mm"
include "ledi.mm"
include "wn.mm"
include "wf.mm"
include "ancom.mm"
include "df-a.mm"
include "2or.mm"
include "ax-r1.mm"
include "con3.mm"
include "ax-r2.mm"
include "con2.mm"
include "2an.mm"
include "anass.mm"
include "ax-a1.mm"
include "bctr.mm"
include "wwcom3ii.mm"
include "anandi.mm"
include "3tr1.mm"
include "lan.mm"
include "an12.mm"
include "oran.mm"
include "dff.mm"
include "an0.mm"
include "wwoml3.mm"

theorem wwfh1
  let wva: term a
  let wvb: term b
  let wvc: term c
  assume wwfh.1: |- b C a
  assume wwfh.2: |- c C a


  assert |- ( ( a ^ ( b v c ) ) == ( ( a ^ b ) v ( a ^ c ) ) ) = 1

  proof
    wva
    wvb
    wvc
    wo
    #
    wa
    #
    wva
    wvb
    wa
    #
    wva
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
    wva
    wvb
    wvc
    ledi
    @1
    @4
    wn
    #
    wa
    #
    wva
    @0
    wvb
    wn
    #
    wvc
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
    @0
    wva
    wa
    #
    wva
    wn
    #
    @7
    wo
    #
    @13
    @8
    wo
    #
    wa
    #
    wa
    #
    @11
    @1
    @12
    @5
    @16
    wva
    @0
    ancom
    @4
    @16
    @4
    @14
    wn
    #
    @15
    wn
    #
    wo
    #
    @16
    wn
    @2
    @18
    @3
    @19
    wva
    wvb
    df-a
    wva
    wvc
    df-a
    2or
    @20
    @16
    @16
    @20
    wn
    @14
    @15
    df-a
    ax-r1
    con3
    ax-r2
    con2
    2an
    @17
    @0
    wva
    @9
    wa
    #
    wa
    #
    @11
    @17
    @0
    wva
    @16
    wa
    #
    wa
    @22
    @0
    wva
    @16
    anass
    @23
    @21
    @0
    wva
    @14
    wa
    #
    wva
    @15
    wa
    #
    wa
    wva
    @7
    wa
    #
    wva
    @8
    wa
    #
    wa
    @23
    @21
    @24
    @26
    @25
    @27
    wva
    @7
    @7
    wn
    #
    wvb
    wva
    wvb
    @28
    wvb
    ax-a1
    ax-r1
    wwfh.1
    bctr
    wwcom3ii
    wva
    @8
    @8
    wn
    #
    wvc
    wva
    wvc
    @29
    wvc
    ax-a1
    ax-r1
    wwfh.2
    bctr
    wwcom3ii
    2an
    wva
    @14
    @15
    anandi
    wva
    @7
    @8
    anandi
    3tr1
    lan
    ax-r2
    @0
    wva
    @9
    an12
    ax-r2
    ax-r2
    @11
    wva
    wf
    wa
    wf
    @10
    wf
    wva
    @10
    @0
    @0
    wn
    #
    wa
    #
    wf
    @9
    @30
    @0
    @9
    @0
    @0
    @9
    wn
    wvb
    wvc
    oran
    ax-r1
    con3
    lan
    wf
    @31
    @0
    dff
    ax-r1
    ax-r2
    lan
    wva
    an0
    ax-r2
    ax-r2
    wwoml3
    ax-r2
end
