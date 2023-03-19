include "ccref.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cref.mm"
include "wbr.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "iscref.mm"
include "simplbi.mm"

theorem creftop
  let cA: class A
  let cJ: class J
  let vy: setvar y
  let vz: setvar z


  assert |- ( J e. CovHasRef A -> J e. Top )

  proof
    cJ
    cA
    ccref
    wcel
    cJ
    ctop
    wcel
    cJ
    cuni
    #
    vy
    cv
    #
    cuni
    wceq
    vz
    cv
    @1
    cref
    wbr
    vz
    cJ
    cpw
    #
    cA
    cin
    wrex
    wi
    vy
    @2
    wral
    vy
    vz
    cA
    cJ
    @0
    @0
    eqid
    iscref
    simplbi
end
