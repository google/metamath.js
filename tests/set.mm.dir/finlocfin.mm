include "ctop.mm"
include "wcel.mm"
include "cfn.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "clocfin.mm"
include "cfv.mm"
include "simp1.mm"
include "simp3.mm"
include "simpl1.mm"
include "topopn.mm"
include "syl.mm"
include "simpr.mm"
include "wss.mm"
include "simpl2.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "eleq2.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "islocfin.mm"
include "syl3anbrc.mm"

theorem finlocfin
  let cA: class A
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  assume finlocfin.1: |- X = U. J
  assume finlocfin.2: |- Y = U. A


  assert |- ( ( J e. Top /\ A e. Fin /\ X = Y ) -> A e. ( LocFin ` J ) )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cfn
    wcel
    #
    cX
    cY
    wceq
    #
    w3a
    #
    @0
    @2
    vx
    cv
    #
    vn
    cv
    #
    wcel
    #
    vs
    cv
    #
    @5
    cin
    #
    c0
    wne
    #
    vs
    cA
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vn
    cJ
    wrex
    #
    vx
    cX
    wral
    cA
    cJ
    clocfin
    cfv
    wcel
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @3
    @13
    vx
    cX
    @3
    @4
    cX
    wcel
    #
    wa
    #
    cX
    cJ
    wcel
    #
    @14
    @7
    cX
    cin
    #
    c0
    wne
    #
    vs
    cA
    crab
    #
    cfn
    wcel
    #
    @13
    @15
    @0
    @16
    @0
    @1
    @2
    @14
    simpl1
    cJ
    cX
    finlocfin.1
    topopn
    syl
    @3
    @14
    simpr
    @15
    @1
    @19
    cA
    wss
    @20
    @0
    @1
    @2
    @14
    simpl2
    @18
    vs
    cA
    ssrab2
    cA
    @19
    ssfi
    sylancl
    @12
    @14
    @20
    wa
    vn
    cX
    cJ
    @5
    cX
    wceq
    #
    @6
    @14
    @11
    @20
    @5
    cX
    @4
    eleq2
    @21
    @10
    @19
    cfn
    @21
    @9
    @18
    vs
    cA
    @21
    @8
    @17
    c0
    @5
    cX
    @7
    ineq2
    neeq1d
    rabbidv
    eleq1d
    anbi12d
    rspcev
    syl12anc
    ralrimiva
    vx
    cA
    vn
    cJ
    cX
    cY
    vs
    finlocfin.1
    finlocfin.2
    islocfin
    syl3anbrc
end
