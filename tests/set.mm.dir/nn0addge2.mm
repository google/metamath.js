include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "addge02.mm"
include "biimp3a.mm"
include "3expb.mm"
include "sylan2.mm"

theorem nn0addge2
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. NN0 ) -> A <_ ( N + A ) )

  proof
    cN
    cn0
    wcel
    #
    cA
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cc0
    cN
    cle
    wbr
    #
    wa
    cA
    cN
    cA
    caddc
    co
    cle
    wbr
    #
    @0
    @2
    @3
    cN
    nn0re
    cN
    nn0ge0
    jca
    @1
    @2
    @3
    @4
    @1
    @2
    @3
    @4
    cA
    cN
    addge02
    biimp3a
    3expb
    sylan2
end
