include "cun.mm"
include "wceq.mm"
include "idn1.mm"
include "uncom.mm"
include "eqeq1.mm"
include "biimprd.mm"
include "e10.mm"
include "in1.mm"
include "eqeq2.mm"
include "biimprcd.mm"
include "impbii.mm"

theorem equncomVD
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = ( B u. C ) <-> A = ( C u. B ) )

  proof
    cA
    cB
    cC
    cun
    #
    wceq
    #
    cA
    cC
    cB
    cun
    #
    wceq
    #
    @1
    @3
    @1
    @1
    @0
    @2
    wceq
    #
    @3
    @1
    idn1
    cB
    cC
    uncom
    #
    @1
    @3
    @4
    cA
    @0
    @2
    eqeq1
    biimprd
    e10
    in1
    @3
    @1
    @3
    @3
    @4
    @1
    @3
    idn1
    @5
    @4
    @1
    @3
    @0
    @2
    cA
    eqeq2
    biimprcd
    e10
    in1
    impbii
end
