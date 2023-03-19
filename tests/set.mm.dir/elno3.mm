include "wfun.mm"
include "cdm.mm"
include "con0.mm"
include "wcel.mm"
include "crn.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "csur.mm"
include "wf.mm"
include "3anan32.mm"
include "elno2.mm"
include "wfn.mm"
include "df-f.mm"
include "funfn.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "3bitr4i.mm"

theorem elno3
  let cA: class A


  assert |- ( A e. No <-> ( A : dom A --> { 1o , 2o } /\ dom A e. On ) )

  proof
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
    @0
    @4
    wa
    #
    @2
    wa
    cA
    csur
    wcel
    @1
    @3
    cA
    wf
    #
    @2
    wa
    @0
    @2
    @4
    3anan32
    cA
    elno2
    @6
    @5
    @2
    @6
    cA
    @1
    wfn
    #
    @4
    wa
    @5
    @1
    @3
    cA
    df-f
    @0
    @7
    @4
    cA
    funfn
    anbi1i
    bitr4i
    anbi1i
    3bitr4i
end
