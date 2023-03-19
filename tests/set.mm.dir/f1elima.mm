include "wf1.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "wfn.mm"
include "f1fn.mm"
include "fvelimab.mm"
include "sylan.mm"
include "3adant2.mm"
include "wi.mm"
include "wa.mm"
include "ssel.mm"
include "impac.mm"
include "f1fveq.mm"
include "ancom2s.mm"
include "biimpd.mm"
include "anassrs.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "sylan9.mm"
include "anasss.mm"
include "sylan2.mm"
include "rexlimdva.mm"
include "3impa.mm"
include "eqid.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "impbid1.mm"
include "bitrd.mm"

theorem f1elima
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let cY: class Y
  let vz: setvar z


  assert |- ( ( F : A -1-1-> B /\ X e. A /\ Y C_ A ) -> ( ( F ` X ) e. ( F " Y ) <-> X e. Y ) )

  proof
    cA
    cB
    cF
    wf1
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wss
    #
    w3a
    #
    cX
    cF
    cfv
    #
    cF
    cY
    cima
    wcel
    #
    vz
    cv
    #
    cF
    cfv
    #
    @4
    wceq
    #
    vz
    cY
    wrex
    #
    cX
    cY
    wcel
    #
    @0
    @2
    @5
    @9
    wb
    #
    @1
    @0
    cF
    cA
    wfn
    @2
    @11
    cA
    cB
    cF
    f1fn
    vz
    cA
    cY
    @4
    cF
    fvelimab
    sylan
    3adant2
    @3
    @9
    @10
    @0
    @1
    @2
    @9
    @10
    wi
    @0
    @1
    wa
    #
    @2
    wa
    @8
    @10
    vz
    cY
    @12
    @2
    @6
    cY
    wcel
    #
    @8
    @10
    wi
    #
    @2
    @13
    wa
    @12
    @6
    cA
    wcel
    #
    @13
    wa
    @14
    @2
    @13
    @15
    cY
    cA
    @6
    ssel
    impac
    @12
    @15
    @13
    @14
    @12
    @15
    wa
    @8
    @6
    cX
    wceq
    #
    @13
    @10
    @0
    @1
    @15
    @8
    @16
    wi
    @0
    @1
    @15
    wa
    wa
    @8
    @16
    @0
    @15
    @1
    @8
    @16
    wb
    cA
    cB
    @6
    cX
    cF
    f1fveq
    ancom2s
    biimpd
    anassrs
    @16
    @13
    @10
    @6
    cX
    cY
    eleq1
    biimpcd
    sylan9
    anasss
    sylan2
    anassrs
    rexlimdva
    3impa
    @10
    @4
    @4
    wceq
    #
    @9
    @4
    eqid
    @8
    @17
    vz
    cX
    cY
    @16
    @7
    @4
    @4
    @6
    cX
    cF
    fveq2
    eqeq1d
    rspcev
    mpan2
    impbid1
    bitrd
end
