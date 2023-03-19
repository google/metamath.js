include "cgru.mm"
include "wcel.mm"
include "wtr.mm"
include "cv.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "crn.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "elgrug.mm"
include "ibi.mm"
include "simpld.mm"

theorem grutr
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( U e. Univ -> Tr U )

  proof
    cU
    cgru
    wcel
    #
    cU
    wtr
    #
    vx
    cv
    #
    cpw
    cU
    wcel
    @2
    vy
    cv
    #
    cpr
    cU
    wcel
    vy
    cU
    wral
    @3
    crn
    cuni
    cU
    wcel
    vy
    cU
    @2
    cmap
    co
    wral
    w3a
    vx
    cU
    wral
    #
    @0
    @1
    @4
    wa
    vx
    vy
    cU
    cgru
    elgrug
    ibi
    simpld
end
