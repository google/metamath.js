include "cv.mm"
include "c0r.mm"
include "cop.mm"
include "caddc.mm"
include "co.mm"
include "cr.mm"
include "wcel.mm"
include "cnr.mm"
include "elreal.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "wa.mm"
include "cplr.mm"
include "addresr.mm"
include "addclsr.mm"
include "opelreal.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "2gencl.mm"

theorem axaddrcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A + B ) e. RR )

  proof
    vx
    cv
    #
    c0r
    cop
    #
    vy
    cv
    #
    c0r
    cop
    #
    caddc
    co
    #
    cr
    wcel
    cA
    @3
    caddc
    co
    #
    cr
    wcel
    cA
    cB
    caddc
    co
    #
    cr
    wcel
    vx
    vy
    @1
    @3
    cA
    cB
    cnr
    cr
    vx
    cA
    elreal
    vy
    cB
    elreal
    @1
    cA
    wceq
    @4
    @5
    cr
    @1
    cA
    @3
    caddc
    oveq1
    eleq1d
    @3
    cB
    wceq
    @5
    @6
    cr
    @3
    cB
    cA
    caddc
    oveq2
    eleq1d
    @0
    cnr
    wcel
    @2
    cnr
    wcel
    wa
    #
    @4
    @0
    @2
    cplr
    co
    #
    c0r
    cop
    #
    cr
    @0
    @2
    addresr
    @7
    @8
    cnr
    wcel
    @9
    cr
    wcel
    @0
    @2
    addclsr
    @8
    opelreal
    sylibr
    eqeltrd
    2gencl
end
