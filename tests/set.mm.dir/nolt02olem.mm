include "csur.mm"
include "wcel.mm"
include "con0.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cdm.mm"
include "wss.mm"
include "wn.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "nosgnn0.mm"
include "a1i.mm"
include "wa.mm"
include "simpl3.mm"
include "crn.mm"
include "simpl1.mm"
include "norn.mm"
include "syl.mm"
include "wfun.mm"
include "nofun.mm"
include "3ad2ant1.mm"
include "fvelrn.mm"
include "sylan.mm"
include "sseldd.mm"
include "eqeltrrd.mm"
include "mtand.mm"
include "wb.mm"
include "nodmon.mm"
include "simp2.mm"
include "ontri1.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem nolt02olem
  let cA: class A
  let cX: class X


  assert |- ( ( A e. No /\ X e. On /\ ( A ` X ) = (/) ) -> dom A C_ X )

  proof
    cA
    csur
    wcel
    #
    cX
    con0
    wcel
    #
    cX
    cA
    cfv
    #
    c0
    wceq
    #
    w3a
    #
    cA
    cdm
    #
    cX
    wss
    #
    cX
    @5
    wcel
    #
    wn
    #
    @4
    @7
    c0
    c1o
    c2o
    cpr
    #
    wcel
    #
    @10
    wn
    @4
    nosgnn0
    a1i
    @4
    @7
    wa
    #
    @2
    c0
    @9
    @0
    @1
    @3
    @7
    simpl3
    @11
    cA
    crn
    #
    @9
    @2
    @11
    @0
    @12
    @9
    wss
    @0
    @1
    @3
    @7
    simpl1
    cA
    norn
    syl
    @4
    cA
    wfun
    #
    @7
    @2
    @12
    wcel
    @0
    @1
    @13
    @3
    cA
    nofun
    3ad2ant1
    cX
    cA
    fvelrn
    sylan
    sseldd
    eqeltrrd
    mtand
    @4
    @5
    con0
    wcel
    #
    @1
    @6
    @8
    wb
    @0
    @1
    @14
    @3
    cA
    nodmon
    3ad2ant1
    @0
    @1
    @3
    simp2
    @5
    cX
    ontri1
    syl2anc
    mpbird
end
