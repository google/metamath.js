include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "cxr.mm"
include "wb.mm"
include "eliooxr.mm"
include "elioo2.mm"
include "syl.mm"
include "ibi.mm"
include "3simpc.mm"

theorem eliooord
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B (,) C ) -> ( B < A /\ A < C ) )

  proof
    cA
    cB
    cC
    cioo
    co
    wcel
    #
    cA
    cr
    wcel
    #
    cB
    cA
    clt
    wbr
    #
    cA
    cC
    clt
    wbr
    #
    w3a
    #
    @2
    @3
    wa
    @0
    @4
    @0
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    wa
    @0
    @4
    wb
    cA
    cB
    cC
    eliooxr
    cB
    cC
    cA
    elioo2
    syl
    ibi
    @1
    @2
    @3
    3simpc
    syl
end
