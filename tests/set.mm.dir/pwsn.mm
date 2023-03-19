include "cv.mm"
include "csn.mm"
include "wss.mm"
include "cab.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "cpw.mm"
include "cpr.mm"
include "sssn.mm"
include "abbii.mm"
include "df-pw.mm"
include "dfpr2.mm"
include "3eqtr4i.mm"

theorem pwsn
  let cA: class A
  let vx: setvar x
  let cB: class B
  let cC: class C


  assert |- ~P { A } = { (/) , { A } }

  proof
    vx
    cv
    #
    cA
    csn
    #
    wss
    #
    vx
    cab
    @0
    c0
    wceq
    @0
    @1
    wceq
    wo
    #
    vx
    cab
    @1
    cpw
    c0
    @1
    cpr
    @2
    @3
    vx
    @0
    cA
    sssn
    abbii
    vx
    @1
    df-pw
    vx
    c0
    @1
    dfpr2
    3eqtr4i
end
