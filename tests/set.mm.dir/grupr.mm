include "cgru.mm"
include "wcel.mm"
include "cpr.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "cpw.mm"
include "crn.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "wtr.mm"
include "wa.mm"
include "elgrug.mm"
include "ibi.mm"
include "simprd.mm"
include "wceq.mm"
include "preq2.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "3ad2ant2.mm"
include "com12.mm"
include "ralimdv.mm"
include "syl5com.mm"
include "preq1.mm"
include "syl6.mm"
include "com23.mm"
include "3imp.mm"

theorem grupr
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U /\ B e. U ) -> { A , B } e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cB
    cU
    wcel
    #
    cA
    cB
    cpr
    #
    cU
    wcel
    #
    @0
    @2
    @1
    @4
    @0
    @2
    vx
    cv
    #
    cB
    cpr
    #
    cU
    wcel
    #
    vx
    cU
    wral
    #
    @1
    @4
    wi
    @0
    @5
    cpw
    cU
    wcel
    #
    @5
    vy
    cv
    #
    cpr
    #
    cU
    wcel
    #
    vy
    cU
    wral
    #
    @10
    crn
    cuni
    cU
    wcel
    vy
    cU
    @5
    cmap
    co
    wral
    #
    w3a
    #
    vx
    cU
    wral
    #
    @2
    @8
    @0
    cU
    wtr
    #
    @16
    @0
    @17
    @16
    wa
    vx
    vy
    cU
    cgru
    elgrug
    ibi
    simprd
    @2
    @15
    @7
    vx
    cU
    @15
    @2
    @7
    @13
    @9
    @2
    @7
    wi
    @14
    @12
    @7
    vy
    cB
    cU
    @10
    cB
    wceq
    @11
    @6
    cU
    @10
    cB
    @5
    preq2
    eleq1d
    rspccv
    3ad2ant2
    com12
    ralimdv
    syl5com
    @7
    @4
    vx
    cA
    cU
    @5
    cA
    wceq
    @6
    @3
    cU
    @5
    cA
    cB
    preq1
    eleq1d
    rspccv
    syl6
    com23
    3imp
end
