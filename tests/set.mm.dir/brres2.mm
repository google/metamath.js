include "cres.mm"
include "crn.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "brresALTV.mm"
include "pm5.32i.mm"
include "relres.mm"
include "relelrni.mm"
include "pm4.71ri.mm"
include "w3a.mm"
include "brinxp2ALTV.mm"
include "df-3an.mm"
include "3anan12.mm"
include "3bitr2i.mm"
include "3bitr4i.mm"

theorem brres2
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R


  assert |- ( B ( R |` A ) C <-> B ( R i^i ( A X. ran ( R |` A ) ) ) C )

  proof
    cC
    cR
    cA
    cres
    #
    crn
    #
    wcel
    #
    cB
    cC
    @0
    wbr
    #
    wa
    @2
    cB
    cA
    wcel
    #
    cB
    cC
    cR
    wbr
    #
    wa
    #
    wa
    #
    @3
    cB
    cC
    cR
    cA
    @1
    cxp
    cin
    wbr
    #
    @2
    @3
    @6
    cA
    cB
    cC
    cR
    @1
    brresALTV
    pm5.32i
    @3
    @2
    cB
    cC
    @0
    cR
    cA
    relres
    relelrni
    pm4.71ri
    @8
    @4
    @2
    wa
    @5
    wa
    @4
    @2
    @5
    w3a
    @7
    cA
    @1
    cB
    cC
    cR
    brinxp2ALTV
    @4
    @2
    @5
    df-3an
    @4
    @2
    @5
    3anan12
    3bitr2i
    3bitr4i
end
