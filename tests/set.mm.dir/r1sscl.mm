include "cr1.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "r1pwss.mm"
include "adantr.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "sseldd.mm"

theorem r1sscl
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ( R1 ` B ) /\ C C_ A ) -> C e. ( R1 ` B ) )

  proof
    cA
    cB
    cr1
    cfv
    #
    wcel
    #
    cC
    cA
    wss
    #
    wa
    cA
    cpw
    #
    @0
    cC
    @1
    @3
    @0
    wss
    @2
    cA
    cB
    r1pwss
    adantr
    @1
    cC
    @3
    wcel
    @2
    cC
    cA
    @0
    elpw2g
    biimpar
    sseldd
end
