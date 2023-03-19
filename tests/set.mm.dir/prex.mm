include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "preq2.mm"
include "eleq1d.mm"
include "zfpair2.mm"
include "vtoclg.mm"
include "preq1.mm"
include "syl5ib.mm"
include "vtocleg.mm"
include "wn.mm"
include "csn.mm"
include "prprc1.mm"
include "snex.mm"
include "syl6eqel.mm"
include "prprc2.mm"
include "pm2.61nii.mm"

theorem prex
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- { A , B } e. _V

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    cpr
    #
    cvv
    wcel
    #
    @1
    @3
    wi
    vx
    cA
    cvv
    @1
    vx
    cv
    #
    cB
    cpr
    #
    cvv
    wcel
    #
    @4
    cA
    wceq
    #
    @3
    @4
    vy
    cv
    #
    cpr
    #
    cvv
    wcel
    @6
    vy
    cB
    cvv
    @8
    cB
    wceq
    @9
    @5
    cvv
    @8
    cB
    @4
    preq2
    eleq1d
    vx
    vy
    zfpair2
    vtoclg
    @7
    @5
    @2
    cvv
    @4
    cA
    cB
    preq1
    eleq1d
    syl5ib
    vtocleg
    @0
    wn
    @2
    cB
    csn
    cvv
    cA
    cB
    prprc1
    cB
    snex
    syl6eqel
    @1
    wn
    @2
    cA
    csn
    cvv
    cA
    cB
    prprc2
    cA
    snex
    syl6eqel
    pm2.61nii
end
