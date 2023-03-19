include "csur.mm"
include "wcel.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "c1o.mm"
include "c2o.mm"
include "wo.mm"
include "w3o.mm"
include "cdm.mm"
include "wn.mm"
include "pm2.1.mm"
include "wi.mm"
include "ndmfv.mm"
include "a1i.mm"
include "wfun.mm"
include "crn.mm"
include "cpr.mm"
include "wss.mm"
include "nofun.mm"
include "norn.mm"
include "wa.mm"
include "fvelrn.mm"
include "ssel.mm"
include "syl5com.mm"
include "impancom.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "2on.mm"
include "elpr2.mm"
include "syl6ib.mm"
include "syl2anc.mm"
include "orim12d.mm"
include "mpi.mm"
include "3orass.mm"
include "sylibr.mm"

theorem nofv
  let cA: class A
  let cX: class X


  assert |- ( A e. No -> ( ( A ` X ) = (/) \/ ( A ` X ) = 1o \/ ( A ` X ) = 2o ) )

  proof
    cA
    csur
    wcel
    #
    cX
    cA
    cfv
    #
    c0
    wceq
    #
    @1
    c1o
    wceq
    #
    @1
    c2o
    wceq
    #
    wo
    #
    wo
    #
    @2
    @3
    @4
    w3o
    @0
    cX
    cA
    cdm
    wcel
    #
    wn
    #
    @7
    wo
    @6
    @7
    pm2.1
    @0
    @8
    @2
    @7
    @5
    @8
    @2
    wi
    @0
    cX
    cA
    ndmfv
    a1i
    @0
    cA
    wfun
    #
    cA
    crn
    #
    c1o
    c2o
    cpr
    #
    wss
    #
    @7
    @5
    wi
    cA
    nofun
    cA
    norn
    @9
    @12
    wa
    @7
    @1
    @11
    wcel
    #
    @5
    @9
    @7
    @12
    @13
    @9
    @7
    wa
    @1
    @10
    wcel
    @12
    @13
    cX
    cA
    fvelrn
    @10
    @11
    @1
    ssel
    syl5com
    impancom
    @1
    c1o
    c2o
    c1o
    con0
    1on
    elexi
    c2o
    con0
    2on
    elexi
    elpr2
    syl6ib
    syl2anc
    orim12d
    mpi
    @2
    @3
    @4
    3orass
    sylibr
end
