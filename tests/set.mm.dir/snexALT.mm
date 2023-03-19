include "cpw.mm"
include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wss.mm"
include "snsspw.mm"
include "ssexg.mm"
include "mpan.mm"
include "wn.mm"
include "pwexg.mm"
include "con3i.mm"
include "c0.mm"
include "wceq.mm"
include "snprc.mm"
include "biimpi.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "syl.mm"
include "pm2.61i.mm"

theorem snexALT
  let cA: class A


  assert |- { A } e. _V

  proof
    cA
    cpw
    #
    cvv
    wcel
    #
    cA
    csn
    #
    cvv
    wcel
    #
    @2
    @0
    wss
    @1
    @3
    cA
    snsspw
    @2
    @0
    cvv
    ssexg
    mpan
    @1
    wn
    cA
    cvv
    wcel
    #
    wn
    #
    @3
    @4
    @1
    cA
    cvv
    pwexg
    con3i
    @5
    @2
    c0
    cvv
    @5
    @2
    c0
    wceq
    cA
    snprc
    biimpi
    0ex
    syl6eqel
    syl
    pm2.61i
end
