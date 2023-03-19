include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "csigagen.mm"
include "cfv.mm"
include "simpr.mm"
include "sssigagen.mm"
include "adantr.mm"
include "sstrd.mm"

theorem sssigagen2
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. V /\ B C_ A ) -> B C_ ( sigaGen ` A ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    wss
    #
    wa
    cB
    cA
    cA
    csigagen
    cfv
    #
    @0
    @1
    simpr
    @0
    cA
    @2
    wss
    @1
    cA
    cV
    sssigagen
    adantr
    sstrd
end
