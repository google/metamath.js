include "cgru.mm"
include "wcel.mm"
include "wf.mm"
include "crn.mm"
include "cuni.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "elmapg.mm"
include "wi.mm"
include "cv.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "w3a.mm"
include "wtr.mm"
include "elgrug.mm"
include "ibi.mm"
include "simprd.mm"
include "wceq.mm"
include "rneq.mm"
include "unieqd.mm"
include "eleq1d.mm"
include "rspccv.mm"
include "3ad2ant3.mm"
include "ralimi.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "imbi1d.mm"
include "3syl.mm"
include "imp.mm"
include "sylbird.mm"
include "3impia.mm"

theorem gruurn
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( U e. Univ /\ A e. U /\ F : A --> U ) -> U. ran F e. U )

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
    cU
    cF
    wf
    #
    cF
    crn
    #
    cuni
    #
    cU
    wcel
    #
    @0
    @1
    wa
    @2
    cF
    cU
    cA
    cmap
    co
    #
    wcel
    #
    @5
    cU
    cA
    cF
    cgru
    cU
    elmapg
    @0
    @1
    @7
    @5
    wi
    #
    @0
    vx
    cv
    #
    cpw
    cU
    wcel
    #
    @9
    vy
    cv
    #
    cpr
    cU
    wcel
    vy
    cU
    wral
    #
    @11
    crn
    #
    cuni
    #
    cU
    wcel
    #
    vy
    cU
    @9
    cmap
    co
    #
    wral
    #
    w3a
    #
    vx
    cU
    wral
    #
    cF
    @16
    wcel
    #
    @5
    wi
    #
    vx
    cU
    wral
    @1
    @8
    wi
    @0
    cU
    wtr
    #
    @19
    @0
    @22
    @19
    wa
    vx
    vy
    cU
    cgru
    elgrug
    ibi
    simprd
    @18
    @21
    vx
    cU
    @17
    @10
    @21
    @12
    @15
    @5
    vy
    cF
    @16
    @11
    cF
    wceq
    #
    @14
    @4
    cU
    @23
    @13
    @3
    @11
    cF
    rneq
    unieqd
    eleq1d
    rspccv
    3ad2ant3
    ralimi
    @21
    @8
    vx
    cA
    cU
    @9
    cA
    wceq
    #
    @20
    @7
    @5
    @24
    @16
    @6
    cF
    @9
    cA
    cU
    cmap
    oveq2
    eleq2d
    imbi1d
    rspccv
    3syl
    imp
    sylbird
    3impia
end
