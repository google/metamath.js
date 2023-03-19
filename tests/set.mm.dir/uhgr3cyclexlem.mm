include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cdm.mm"
include "cpr.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "wb.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "prcom.mm"
include "eqeq1i.mm"
include "simpl.mm"
include "simpr.mm"
include "preq1b.mm"
include "biimpcd.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "adantl.mm"
include "com12.mm"
include "adantld.mm"
include "com14.mm"
include "imp32.mm"
include "necon3d.mm"
include "impancom.mm"
include "imp.mm"

theorem uhgr3cyclexlem
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  assume uhgr3cyclex.v: |- V = ( Vtx ` G )
  assume uhgr3cyclex.e: |- E = ( Edg ` G )
  assume uhgr3cyclex.i: |- I = ( iEdg ` G )


  assert |- ( ( ( ( A e. V /\ B e. V ) /\ A =/= B ) /\ ( ( J e. dom I /\ { B , C } = ( I ` J ) ) /\ ( K e. dom I /\ { C , A } = ( I ` K ) ) ) ) -> J =/= K )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    wa
    cJ
    cI
    cdm
    #
    wcel
    #
    cB
    cC
    cpr
    #
    cJ
    cI
    cfv
    #
    wceq
    #
    wa
    #
    cK
    @4
    wcel
    #
    cC
    cA
    cpr
    #
    cK
    cI
    cfv
    #
    wceq
    #
    wa
    #
    wa
    #
    cJ
    cK
    wne
    #
    @2
    @15
    @3
    @16
    @2
    @15
    wa
    cJ
    cK
    cA
    cB
    @2
    @9
    @14
    cJ
    cK
    wceq
    #
    cA
    cB
    wceq
    #
    wi
    @17
    @9
    @14
    @2
    @18
    @17
    @8
    @14
    @2
    @18
    wi
    #
    wi
    #
    @5
    @17
    @8
    @6
    @12
    wceq
    #
    @20
    @17
    @7
    @12
    @6
    cJ
    cK
    cI
    fveq2
    eqeq2d
    @14
    @21
    @19
    @13
    @21
    @19
    wi
    @10
    @13
    @21
    @6
    @11
    wceq
    #
    @19
    @21
    @22
    wb
    @12
    @11
    @12
    @11
    @6
    eqeq2
    eqcoms
    @19
    @11
    @6
    @11
    @6
    wceq
    cA
    cC
    cpr
    #
    @6
    wceq
    #
    @19
    @11
    @23
    @6
    cC
    cA
    prcom
    eqeq1i
    @2
    @24
    @18
    @2
    cA
    cB
    cC
    cV
    cV
    @0
    @1
    simpl
    @0
    @1
    simpr
    preq1b
    biimpcd
    sylbi
    eqcoms
    syl6bi
    adantl
    com12
    syl6bi
    adantld
    com14
    imp32
    necon3d
    impancom
    imp
end
