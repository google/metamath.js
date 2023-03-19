include "wceq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "sneqd.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "ifpbi123d.mm"

theorem wkslem1
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cI: class I


  assert |- ( A = B -> ( if- ( ( P ` A ) = ( P ` ( A + 1 ) ) , ( I ` ( F ` A ) ) = { ( P ` A ) } , { ( P ` A ) , ( P ` ( A + 1 ) ) } C_ ( I ` ( F ` A ) ) ) <-> if- ( ( P ` B ) = ( P ` ( B + 1 ) ) , ( I ` ( F ` B ) ) = { ( P ` B ) } , { ( P ` B ) , ( P ` ( B + 1 ) ) } C_ ( I ` ( F ` B ) ) ) ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cP
    cfv
    #
    cA
    c1
    caddc
    co
    #
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
    @1
    csn
    #
    wceq
    @1
    @3
    cpr
    #
    @5
    wss
    cB
    cP
    cfv
    #
    cB
    c1
    caddc
    co
    #
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
    @8
    csn
    #
    wceq
    @8
    @10
    cpr
    #
    @12
    wss
    @0
    @1
    @8
    @3
    @10
    cA
    cB
    cP
    fveq2
    #
    @0
    @2
    @9
    cP
    cA
    cB
    c1
    caddc
    oveq1
    fveq2d
    #
    eqeq12d
    @0
    @5
    @12
    @6
    @13
    @0
    @4
    @11
    cI
    cA
    cB
    cF
    fveq2
    fveq2d
    #
    @0
    @1
    @8
    @15
    sneqd
    eqeq12d
    @0
    @7
    @14
    @5
    @12
    @0
    @1
    @8
    @3
    @10
    @15
    @16
    preq12d
    @17
    sseq12d
    ifpbi123d
end
