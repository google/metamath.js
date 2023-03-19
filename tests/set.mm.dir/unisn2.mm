include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "cuni.mm"
include "c0.mm"
include "cpr.mm"
include "unisng.mm"
include "prid2g.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wceq.mm"
include "snprc.mm"
include "biimpi.mm"
include "unieqd.mm"
include "uni0.mm"
include "0ex.mm"
include "prid1.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"

theorem unisn2
  let cA: class A


  assert |- U. { A } e. { (/) , A }

  proof
    cA
    cvv
    wcel
    #
    cA
    csn
    #
    cuni
    #
    c0
    cA
    cpr
    #
    wcel
    @0
    @2
    cA
    @3
    cA
    cvv
    unisng
    c0
    cA
    cvv
    prid2g
    eqeltrd
    @0
    wn
    #
    @2
    c0
    cuni
    #
    @3
    @4
    @1
    c0
    @4
    @1
    c0
    wceq
    cA
    snprc
    biimpi
    unieqd
    @5
    c0
    @3
    uni0
    c0
    cA
    0ex
    prid1
    eqeltri
    syl6eqel
    pm2.61i
end
