include "cgru.mm"
include "wcel.mm"
include "cpw.mm"
include "cv.mm"
include "cpr.mm"
include "wral.mm"
include "crn.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "wi.mm"
include "wtr.mm"
include "wa.mm"
include "elgrug.mm"
include "ibi.mm"
include "simprd.mm"
include "simp1.mm"
include "ralimi.mm"
include "wceq.mm"
include "pweq.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "3syl.mm"
include "imp.mm"

theorem grupw
  let cA: class A
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cF: class F


  assert |- ( ( U e. Univ /\ A e. U ) -> ~P A e. U )

  proof
    cU
    cgru
    wcel
    #
    cA
    cU
    wcel
    #
    cA
    cpw
    #
    cU
    wcel
    #
    @0
    vy
    cv
    #
    cpw
    #
    cU
    wcel
    #
    @4
    vx
    cv
    #
    cpr
    cU
    wcel
    vx
    cU
    wral
    #
    @7
    crn
    cuni
    cU
    wcel
    vx
    cU
    @4
    cmap
    co
    wral
    #
    w3a
    #
    vy
    cU
    wral
    #
    @6
    vy
    cU
    wral
    @1
    @3
    wi
    @0
    cU
    wtr
    #
    @11
    @0
    @12
    @11
    wa
    vy
    vx
    cU
    cgru
    elgrug
    ibi
    simprd
    @10
    @6
    vy
    cU
    @6
    @8
    @9
    simp1
    ralimi
    @6
    @3
    vy
    cA
    cU
    @4
    cA
    wceq
    @5
    @2
    cU
    @4
    cA
    pweq
    eleq1d
    rspccv
    3syl
    imp
end
