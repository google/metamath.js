include "tb.mm"
include "wo.mm"
include "wa.mm"
include "wn.mm"
include "dfb.mm"
include "bile.mm"
include "mlaconjolem.mm"
include "le2an.mm"
include "lea.mm"
include "le2or.mm"
include "leao1.mm"
include "oran.mm"
include "lbtr.mm"
include "lecom.mm"
include "comcom7.mm"
include "leor.mm"
include "df-a.mm"
include "lor.mm"
include "oran1.mm"
include "ax-r2.mm"
include "lear.mm"
include "mh.mm"
include "wf.mm"
include "an12.mm"
include "oran3.mm"
include "lan.mm"
include "dff.mm"
include "ax-r1.mm"
include "an0.mm"
include "3tr.mm"
include "or0.mm"
include "ax-r5.mm"
include "or0r.mm"
include "2or.mm"
include "le3tr1.mm"
include "letr.mm"

theorem mlaconjo
  param wva: term a
  param wvb: term b
  param wvc: term c


  assert |- ( ( a == b ) ^ ( ( a == c ) v ( b == c ) ) ) =< ( a == c )

  proof
    wva
    wvb
    tb
    #
    wva
    wvc
    tb
    #
    wvb
    wvc
    tb
    wo
    #
    wa
    wva
    wvb
    wa
    #
    wva
    wn
    #
    wvb
    wn
    #
    wa
    #
    wo
    #
    wvc
    wva
    wvb
    wo
    #
    wa
    #
    wvc
    wn
    #
    @4
    @5
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    @1
    @0
    @7
    @2
    @13
    @0
    @7
    wva
    wvb
    dfb
    bile
    wva
    wvb
    wvc
    mlaconjolem
    le2an
    @3
    @9
    wa
    #
    @6
    @12
    wa
    #
    wo
    #
    wva
    wvc
    wa
    #
    @4
    @10
    wa
    #
    wo
    @14
    @1
    @15
    @18
    @16
    @19
    @3
    wva
    @9
    wvc
    wva
    wvb
    lea
    wvc
    @8
    lea
    le2an
    @6
    @4
    @12
    @10
    @4
    @5
    lea
    @10
    @11
    lea
    le2an
    le2or
    @14
    @15
    @3
    @12
    wa
    #
    wo
    #
    @6
    @9
    wa
    #
    @16
    wo
    #
    wo
    @17
    @3
    @9
    @6
    @12
    @3
    @6
    @3
    @6
    wn
    #
    @3
    @8
    @24
    wva
    wvb
    wvb
    leao1
    wva
    wvb
    oran
    #
    lbtr
    lecom
    comcom7
    @3
    @12
    @3
    @12
    wn
    #
    @3
    wvc
    @3
    wo
    #
    @26
    @3
    wvc
    leor
    @27
    wvc
    @11
    wn
    #
    wo
    #
    @26
    @3
    @28
    wvc
    wva
    wvb
    df-a
    lor
    wvc
    @11
    oran1
    #
    ax-r2
    lbtr
    lecom
    comcom7
    @9
    @6
    @9
    @24
    @9
    @8
    @24
    wvc
    @8
    lear
    @25
    lbtr
    lecom
    comcom7
    @9
    @12
    @9
    @26
    @9
    @29
    @26
    wvc
    @8
    @28
    leao1
    @30
    lbtr
    lecom
    comcom7
    mh
    @21
    @15
    @23
    @16
    @21
    @15
    wf
    wo
    @15
    @20
    wf
    @15
    @20
    @10
    @3
    @11
    wa
    #
    wa
    @10
    wf
    wa
    wf
    @3
    @10
    @11
    an12
    @31
    wf
    @10
    @31
    @3
    @3
    wn
    #
    wa
    #
    wf
    @11
    @32
    @3
    wva
    wvb
    oran3
    lan
    wf
    @33
    @3
    dff
    ax-r1
    ax-r2
    lan
    @10
    an0
    3tr
    lor
    @15
    or0
    ax-r2
    @23
    wf
    @16
    wo
    @16
    @22
    wf
    @16
    @22
    wvc
    @6
    @8
    wa
    #
    wa
    wvc
    wf
    wa
    wf
    @6
    wvc
    @8
    an12
    @34
    wf
    wvc
    @34
    @6
    @24
    wa
    #
    wf
    @8
    @24
    @6
    @25
    lan
    wf
    @35
    @6
    dff
    ax-r1
    ax-r2
    lan
    wvc
    an0
    3tr
    ax-r5
    @16
    or0r
    ax-r2
    2or
    ax-r2
    wva
    wvc
    dfb
    le3tr1
    letr
end
