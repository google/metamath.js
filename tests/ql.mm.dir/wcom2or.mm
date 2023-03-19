include "wo.mm"
include "wa.mm"
include "wn.mm"
include "wcomcom.mm"
include "wdf-c2.mm"
include "ancom.mm"
include "2or.mm"
include "bi1.mm"
include "wr2.mm"
include "w2or.mm"
include "or4.mm"
include "wfh1.mm"
include "wcomcom3.mm"
include "wr1.mm"
include "wdf-c1.mm"

theorem wcom2or
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume wfh.1: |- C ( a , b ) = 1
  assume wfh.2: |- C ( a , c ) = 1


  assert |- C ( a , ( b v c ) ) = 1

  proof
    wvb
    wvc
    wo
    #
    wva
    @0
    wva
    @0
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
    wva
    wn
    #
    wvb
    wa
    #
    @4
    wvc
    wa
    #
    wo
    #
    wo
    #
    @0
    wva
    wa
    #
    @0
    @4
    wa
    #
    wo
    #
    @0
    @1
    @5
    wo
    #
    @2
    @6
    wo
    #
    wo
    #
    @8
    wvb
    @12
    wvc
    @13
    wvb
    wvb
    wva
    wa
    #
    wvb
    @4
    wa
    #
    wo
    #
    @12
    wvb
    wva
    wva
    wvb
    wfh.1
    wcomcom
    wdf-c2
    @17
    @12
    @15
    @1
    @16
    @5
    wvb
    wva
    ancom
    wvb
    @4
    ancom
    2or
    bi1
    wr2
    wvc
    wvc
    wva
    wa
    #
    wvc
    @4
    wa
    #
    wo
    #
    @13
    wvc
    wva
    wva
    wvc
    wfh.2
    wcomcom
    wdf-c2
    @20
    @13
    @18
    @2
    @19
    @6
    wvc
    wva
    ancom
    wvc
    @4
    ancom
    2or
    bi1
    wr2
    w2or
    @14
    @8
    @1
    @5
    @2
    @6
    or4
    bi1
    wr2
    @11
    @8
    @9
    @3
    @10
    @7
    @9
    wva
    @0
    wa
    #
    @3
    @9
    @21
    @0
    wva
    ancom
    bi1
    wva
    wvb
    wvc
    wfh.1
    wfh.2
    wfh1
    wr2
    @10
    @4
    @0
    wa
    #
    @7
    @10
    @22
    @0
    @4
    ancom
    bi1
    @4
    wvb
    wvc
    wva
    wvb
    wfh.1
    wcomcom3
    wva
    wvc
    wfh.2
    wcomcom3
    wfh1
    wr2
    w2or
    wr1
    wr2
    wdf-c1
    wcomcom
end
