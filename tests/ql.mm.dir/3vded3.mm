include "wi0.mm"
include "wn.mm"
include "wo.mm"
include "wt.mm"
include "df-i0.mm"
include "ax-a3.mm"
include "wa.mm"
include "wcmtr.mm"
include "cmtrcom.mm"
include "lor.mm"
include "3tr1.mm"
include "ax-r2.mm"
include "i0cmtrcom.mm"
include "comcom4.mm"
include "comcom.mm"
include "comid.mm"
include "comcom3.mm"
include "fh1.mm"
include "ax-r1.mm"
include "lan.mm"
include "wf.mm"
include "dff.mm"
include "ancom.mm"
include "or0.mm"
include "3tr2.mm"
include "an1.mm"
include "orabs.mm"
include "ax-r5.mm"
include "3tr.mm"

theorem 3vded3
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume 3vded3.1: |- ( c ->0 C ( a , c ) ) = 1
  assume 3vded3.2: |- ( c ->0 a ) = 1
  assume 3vded3.3: |- ( c ->0 ( a ->0 b ) ) = 1


  assert |- ( c ->0 b ) = 1

  proof
    wvc
    wvb
    wi0
    wvc
    wn
    #
    wvb
    wo
    #
    wvc
    wva
    wvb
    wi0
    #
    wi0
    #
    wt
    wvc
    wvb
    df-i0
    @0
    wva
    wn
    #
    wo
    #
    wvb
    wo
    #
    @0
    @4
    wvb
    wo
    #
    wo
    #
    @1
    @3
    @0
    @4
    wvb
    ax-a3
    @6
    @1
    @5
    @0
    wvb
    @5
    @0
    @0
    @4
    wa
    #
    wo
    @0
    @4
    @9
    @0
    @4
    wt
    wa
    #
    @4
    @0
    wa
    #
    @4
    @9
    @4
    @0
    wva
    wo
    #
    wa
    @11
    @4
    wva
    wa
    #
    wo
    #
    @10
    @11
    @4
    @0
    wva
    @0
    @4
    wvc
    wva
    wvc
    wva
    wvc
    wvc
    wva
    wcmtr
    #
    wi0
    #
    wvc
    wva
    wvc
    wcmtr
    #
    wi0
    #
    wt
    @0
    @15
    wo
    @0
    @17
    wo
    @16
    @18
    @15
    @17
    @0
    wvc
    wva
    cmtrcom
    lor
    wvc
    @15
    df-i0
    wvc
    @17
    df-i0
    3tr1
    3vded3.1
    ax-r2
    i0cmtrcom
    comcom4
    comcom
    wva
    wva
    wva
    comid
    comcom3
    fh1
    @12
    wt
    @4
    @12
    wvc
    wva
    wi0
    #
    wt
    @19
    @12
    wvc
    wva
    df-i0
    ax-r1
    3vded3.2
    ax-r2
    lan
    @14
    @11
    wf
    wo
    #
    @11
    @20
    @14
    wf
    @13
    @11
    wf
    wva
    @4
    wa
    @13
    wva
    dff
    wva
    @4
    ancom
    ax-r2
    lor
    ax-r1
    @11
    or0
    ax-r2
    3tr2
    @4
    an1
    @4
    @0
    ancom
    3tr2
    lor
    @0
    @4
    orabs
    ax-r2
    ax-r5
    ax-r1
    @3
    @0
    @2
    wo
    @8
    wvc
    @2
    df-i0
    @2
    @7
    @0
    wva
    wvb
    df-i0
    lor
    ax-r2
    3tr1
    3vded3.3
    3tr
end
