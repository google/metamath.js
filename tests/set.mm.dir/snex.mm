include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cpr.mm"
include "dfsn2.mm"
include "cv.mm"
include "wceq.mm"
include "preq12.mm"
include "anidms.mm"
include "eleq1d.mm"
include "zfpair2.mm"
include "vtoclg.mm"
include "syl5eqel.mm"
include "wn.mm"
include "c0.mm"
include "snprc.mm"
include "biimpi.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem snex
  let cA: class A
  let vx: setvar x


  assert |- { A } e. _V

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    cvv
    wcel
    @0
    @1
    cA
    cA
    cpr
    #
    cvv
    cA
    dfsn2
    vx
    cv
    #
    @3
    cpr
    #
    cvv
    wcel
    @2
    cvv
    wcel
    vx
    cA
    cvv
    @3
    cA
    wceq
    #
    @4
    @2
    cvv
    @5
    @4
    @2
    wceq
    @3
    @3
    cA
    cA
    preq12
    anidms
    eleq1d
    vx
    vx
    zfpair2
    vtoclg
    syl5eqel
    @0
    wn
    #
    @1
    c0
    cvv
    @6
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    0ex
    syl6eqel
    pm2.61i
end
