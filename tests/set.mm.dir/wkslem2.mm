include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "fveq2.mm"
include "adantr.mm"
include "adantl.mm"
include "eqeq12d.mm"
include "wb.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "ifpbi123d.mm"

theorem wkslem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cF: class F
  let cI: class I


  assert |- ( ( A = B /\ ( A + 1 ) = C ) -> ( if- ( ( P ` A ) = ( P ` ( A + 1 ) ) , ( I ` ( F ` A ) ) = { ( P ` A ) } , { ( P ` A ) , ( P ` ( A + 1 ) ) } C_ ( I ` ( F ` A ) ) ) <-> if- ( ( P ` B ) = ( P ` C ) , ( I ` ( F ` B ) ) = { ( P ` B ) } , { ( P ` B ) , ( P ` C ) } C_ ( I ` ( F ` B ) ) ) ) )

  proof
    cA
    cB
    wceq
    #
    cA
    c1
    caddc
    co
    #
    cC
    wceq
    #
    wa
    #
    cA
    cP
    cfv
    #
    @1
    cP
    cfv
    #
    wceq
    cA
    cF
    cfv
    #
    cI
    cfv
    #
    @4
    csn
    #
    wceq
    #
    @4
    @5
    cpr
    #
    @7
    wss
    cB
    cP
    cfv
    #
    cC
    cP
    cfv
    #
    wceq
    cB
    cF
    cfv
    #
    cI
    cfv
    #
    @11
    csn
    #
    wceq
    #
    @11
    @12
    cpr
    #
    @14
    wss
    @3
    @4
    @11
    @5
    @12
    @0
    @4
    @11
    wceq
    @2
    cA
    cB
    cP
    fveq2
    #
    adantr
    #
    @2
    @5
    @12
    wceq
    @0
    @1
    cC
    cP
    fveq2
    adantl
    #
    eqeq12d
    @0
    @9
    @16
    wb
    @2
    @0
    @7
    @14
    @8
    @15
    @0
    @6
    @13
    cI
    cA
    cB
    cF
    fveq2
    fveq2d
    #
    @0
    @4
    @11
    @18
    sneqd
    eqeq12d
    adantr
    @3
    @10
    @17
    @7
    @14
    @3
    @4
    @11
    @5
    @12
    @19
    @20
    preq12d
    @0
    @7
    @14
    wceq
    @2
    @21
    adantr
    sseq12d
    ifpbi123d
end
