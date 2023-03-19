include "csur.mm"
include "wcel.mm"
include "wfun.mm"
include "cdm.mm"
include "con0.mm"
include "crn.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wss.mm"
include "w3a.mm"
include "nofun.mm"
include "nodmon.mm"
include "norn.mm"
include "3jca.mm"
include "cv.mm"
include "wf.mm"
include "wrex.mm"
include "simp2.mm"
include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "simpl.mm"
include "eqidd.mm"
include "df-fn.mm"
include "sylanbrc.mm"
include "anim1i.mm"
include "3impa.mm"
include "df-f.mm"
include "sylibr.mm"
include "feq2.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "elno.mm"
include "impbii.mm"

theorem elno2
  let cA: class A
  let vx: setvar x


  assert |- ( A e. No <-> ( Fun A /\ dom A e. On /\ ran A C_ { 1o , 2o } ) )

  proof
    cA
    csur
    wcel
    #
    cA
    wfun
    #
    cA
    cdm
    #
    con0
    wcel
    #
    cA
    crn
    c1o
    c2o
    cpr
    #
    wss
    #
    w3a
    #
    @0
    @1
    @3
    @5
    cA
    nofun
    cA
    nodmon
    cA
    norn
    3jca
    @6
    vx
    cv
    #
    @4
    cA
    wf
    #
    vx
    con0
    wrex
    #
    @0
    @6
    @3
    @2
    @4
    cA
    wf
    #
    @9
    @1
    @3
    @5
    simp2
    @6
    cA
    @2
    wfn
    #
    @5
    wa
    #
    @10
    @1
    @3
    @5
    @12
    @1
    @3
    wa
    #
    @11
    @5
    @13
    @1
    @2
    @2
    wceq
    @11
    @1
    @3
    simpl
    @13
    @2
    eqidd
    cA
    @2
    df-fn
    sylanbrc
    anim1i
    3impa
    @2
    @4
    cA
    df-f
    sylibr
    @8
    @10
    vx
    @2
    con0
    @7
    @2
    @4
    cA
    feq2
    rspcev
    syl2anc
    vx
    cA
    elno
    sylibr
    impbii
end
