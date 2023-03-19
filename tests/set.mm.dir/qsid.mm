include "cep.mm"
include "ccnv.mm"
include "cqs.mm"
include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wrex.mm"
include "wcel.mm"
include "vex.mm"
include "ecid.mm"
include "eqeq2i.mm"
include "equcom.mm"
include "bitri.mm"
include "rexbii.mm"
include "elqs.mm"
include "risset.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem qsid
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A /. `' _E ) = A

  proof
    vy
    cA
    cep
    ccnv
    #
    cqs
    #
    cA
    vy
    cv
    #
    vx
    cv
    #
    @0
    cec
    #
    wceq
    #
    vx
    cA
    wrex
    @3
    @2
    wceq
    #
    vx
    cA
    wrex
    @2
    @1
    wcel
    @2
    cA
    wcel
    @5
    @6
    vx
    cA
    @5
    @2
    @3
    wceq
    @6
    @4
    @3
    @2
    @3
    vx
    vex
    ecid
    eqeq2i
    vy
    vx
    equcom
    bitri
    rexbii
    vx
    cA
    @2
    @0
    vy
    vex
    elqs
    vx
    @2
    cA
    risset
    3bitr4i
    eqriv
end
