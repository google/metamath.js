include "wfn.mm"
include "cin.mm"
include "cres.mm"
include "fnresin1.mm"
include "resindi.mm"
include "fnresdm.mm"
include "ineq1d.mm"
include "incom.mm"
include "wss.mm"
include "wceq.mm"
include "resss.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "fneq1d.mm"
include "mpbid.mm"

theorem fnresin
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F Fn A -> ( F |` B ) Fn ( A i^i B ) )

  proof
    cF
    cA
    wfn
    #
    cF
    cA
    cB
    cin
    #
    cres
    #
    @1
    wfn
    cF
    cB
    cres
    #
    @1
    wfn
    cA
    cB
    cF
    fnresin1
    @0
    @1
    @2
    @3
    @0
    @2
    cF
    cA
    cres
    #
    @3
    cin
    #
    @3
    cF
    cA
    cB
    resindi
    @0
    @5
    cF
    @3
    cin
    #
    @3
    @0
    @4
    cF
    @3
    cA
    cF
    fnresdm
    ineq1d
    @3
    cF
    cin
    #
    @6
    @3
    @3
    cF
    incom
    @3
    cF
    wss
    @7
    @3
    wceq
    cF
    cB
    resss
    @3
    cF
    df-ss
    mpbi
    eqtr3i
    syl6eq
    syl5eq
    fneq1d
    mpbid
end
