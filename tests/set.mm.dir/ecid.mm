include "cep.mm"
include "ccnv.mm"
include "cec.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "vex.mm"
include "elec.mm"
include "brcnv.mm"
include "epelc.mm"
include "3bitri.mm"
include "eqriv.mm"

theorem ecid
  let cA: class A
  let vy: setvar y
  assume ecid.1: |- A e. _V


  assert |- [ A ] `' _E = A

  proof
    vy
    cA
    cep
    ccnv
    #
    cec
    #
    cA
    vy
    cv
    #
    @1
    wcel
    cA
    @2
    @0
    wbr
    @2
    cA
    cep
    wbr
    @2
    cA
    wcel
    @2
    cA
    @0
    vy
    vex
    #
    ecid.1
    elec
    cA
    @2
    cep
    ecid.1
    @3
    brcnv
    @2
    cA
    ecid.1
    epelc
    3bitri
    eqriv
end
