include "wcel.mm"
include "wfun.mm"
include "cuhgr.mm"
include "w3a.mm"
include "csubgr.mm"
include "wbr.mm"
include "wss.mm"
include "wa.mm"
include "cedg.mm"
include "cfv.mm"
include "cpw.mm"
include "eqid.mm"
include "subgrprop2.mm"
include "3simpa.mm"
include "syl.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "simprl.mm"
include "simp2.mm"
include "simpr.mm"
include "funssres.mm"
include "syl2an.mm"
include "eqcomd.mm"
include "cv.mm"
include "cvtx.mm"
include "edguhgr.mm"
include "ex.mm"
include "pweqi.mm"
include "eleq2i.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "wb.mm"
include "issubgr.mm"
include "3adant2.mm"
include "mpbir3and.mm"
include "impbid2.mm"

theorem uhgrissubgr
  let cA: class A
  let cB: class B
  let cS: class S
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let ve: setvar e
  assume uhgrissubgr.v: |- V = ( Vtx ` S )
  assume uhgrissubgr.a: |- A = ( Vtx ` G )
  assume uhgrissubgr.i: |- I = ( iEdg ` S )
  assume uhgrissubgr.b: |- B = ( iEdg ` G )


  assert |- ( ( G e. W /\ Fun B /\ S e. UHGraph ) -> ( S SubGraph G <-> ( V C_ A /\ I C_ B ) ) )

  proof
    cG
    cW
    wcel
    #
    cB
    wfun
    #
    cS
    cuhgr
    wcel
    #
    w3a
    #
    cS
    cG
    csubgr
    wbr
    #
    cV
    cA
    wss
    #
    cI
    cB
    wss
    #
    wa
    #
    @4
    @5
    @6
    cS
    cedg
    cfv
    #
    cV
    cpw
    #
    wss
    #
    w3a
    @7
    cA
    cB
    cS
    @8
    cG
    cI
    cV
    uhgrissubgr.v
    uhgrissubgr.a
    uhgrissubgr.i
    uhgrissubgr.b
    @8
    eqid
    #
    subgrprop2
    @5
    @6
    @10
    3simpa
    syl
    @3
    @7
    @4
    @3
    @7
    wa
    #
    @4
    @5
    cI
    cB
    cI
    cdm
    cres
    #
    wceq
    #
    @10
    @3
    @5
    @6
    simprl
    @12
    @13
    cI
    @3
    @1
    @6
    @13
    cI
    wceq
    @7
    @0
    @1
    @2
    simp2
    @5
    @6
    simpr
    cB
    cI
    funssres
    syl2an
    eqcomd
    @3
    @10
    @7
    @2
    @0
    @10
    @1
    @2
    ve
    @8
    @9
    @2
    ve
    cv
    #
    @8
    wcel
    #
    @15
    cS
    cvtx
    cfv
    #
    cpw
    #
    wcel
    #
    @15
    @9
    wcel
    @2
    @16
    @19
    @15
    cS
    edguhgr
    ex
    @9
    @18
    @15
    cV
    @17
    uhgrissubgr.v
    pweqi
    eleq2i
    syl6ibr
    ssrdv
    3ad2ant3
    adantr
    @3
    @4
    @5
    @14
    @10
    w3a
    wb
    #
    @7
    @0
    @2
    @20
    @1
    cA
    cB
    cS
    cuhgr
    @8
    cG
    cI
    cV
    cW
    uhgrissubgr.v
    uhgrissubgr.a
    uhgrissubgr.i
    uhgrissubgr.b
    @11
    issubgr
    3adant2
    adantr
    mpbir3and
    ex
    impbid2
end
