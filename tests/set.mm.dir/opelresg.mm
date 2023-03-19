include "wcel.mm"
include "cop.mm"
include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "wa.mm"
include "wb.mm"
include "df-res.mm"
include "eleq2i.mm"
include "a1i.mm"
include "elin.mm"
include "opelxp.mm"
include "elex.mm"
include "biid.mm"
include "rbaib.mm"
include "syl.mm"
include "syl5bb.mm"
include "anbi2d.mm"
include "3bitrd.mm"

theorem opelresg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( B e. V -> ( <. A , B >. e. ( C |` D ) <-> ( <. A , B >. e. C /\ A e. D ) ) )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    cop
    #
    cC
    cD
    cres
    #
    wcel
    #
    @1
    cC
    cD
    cvv
    cxp
    #
    cin
    #
    wcel
    #
    @1
    cC
    wcel
    #
    @1
    @4
    wcel
    #
    wa
    #
    @7
    cA
    cD
    wcel
    #
    wa
    @3
    @6
    wb
    @0
    @2
    @5
    @1
    cC
    cD
    df-res
    eleq2i
    a1i
    @6
    @9
    wb
    @0
    @1
    cC
    @4
    elin
    a1i
    @0
    @8
    @10
    @7
    @8
    @10
    cB
    cvv
    wcel
    #
    wa
    #
    @0
    @10
    cA
    cB
    cD
    cvv
    opelxp
    @0
    @11
    @12
    @10
    wb
    cB
    cV
    elex
    @12
    @10
    @11
    @12
    biid
    rbaib
    syl
    syl5bb
    anbi2d
    3bitrd
end
