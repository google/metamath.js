include "wiso.mm"
include "cxp.mm"
include "cin.mm"
include "ccnv.mm"
include "isocnv.mm"
include "isores2.mm"
include "sylib.mm"
include "syl.mm"
include "wf1o.mm"
include "wrel.mm"
include "wb.mm"
include "isof1o.mm"
include "f1orel.mm"
include "wceq.mm"
include "dfrel2.mm"
include "isoeq1.mm"
include "sylbi.mm"
include "3syl.mm"
include "mpbid.mm"
include "sylibr.mm"
include "impbii.mm"

theorem isores1
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H


  assert |- ( H Isom R , S ( A , B ) <-> H Isom ( R i^i ( A X. A ) ) , S ( A , B ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cA
    cB
    cR
    cA
    cA
    cxp
    cin
    #
    cS
    cH
    wiso
    #
    @0
    cA
    cB
    @1
    cS
    cH
    ccnv
    #
    ccnv
    #
    wiso
    #
    @2
    @0
    cB
    cA
    cS
    @1
    @3
    wiso
    #
    @5
    @0
    cB
    cA
    cS
    cR
    @3
    wiso
    #
    @6
    cA
    cB
    cR
    cS
    cH
    isocnv
    cB
    cA
    cS
    cR
    @3
    isores2
    #
    sylib
    cB
    cA
    cS
    @1
    @3
    isocnv
    syl
    @0
    cA
    cB
    cH
    wf1o
    #
    cH
    wrel
    #
    @5
    @2
    wb
    #
    cA
    cB
    cR
    cS
    cH
    isof1o
    cA
    cB
    cH
    f1orel
    #
    @10
    @4
    cH
    wceq
    #
    @11
    cH
    dfrel2
    #
    cA
    cB
    @1
    cS
    cH
    @4
    isoeq1
    sylbi
    3syl
    mpbid
    @2
    cA
    cB
    cR
    cS
    @4
    wiso
    #
    @0
    @2
    @7
    @15
    @2
    @6
    @7
    cA
    cB
    @1
    cS
    cH
    isocnv
    @8
    sylibr
    cB
    cA
    cS
    cR
    @3
    isocnv
    syl
    @2
    @9
    @10
    @15
    @0
    wb
    #
    cA
    cB
    @1
    cS
    cH
    isof1o
    @12
    @10
    @13
    @16
    @14
    cA
    cB
    cR
    cS
    cH
    @4
    isoeq1
    sylbi
    3syl
    mpbid
    impbii
end
