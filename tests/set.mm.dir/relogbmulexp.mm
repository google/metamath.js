include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "crp.mm"
include "cr.mm"
include "w3a.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "cmul.mm"
include "clogb.mm"
include "caddc.mm"
include "wceq.mm"
include "simp1.mm"
include "rpcxpcl.mm"
include "3adant1.mm"
include "jca.mm"
include "relogbmul.mm"
include "sylan2.mm"
include "relogbreexp.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem relogbmulexp
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ ( A e. RR+ /\ C e. RR+ /\ E e. RR ) ) -> ( B logb ( A x. ( C ^c E ) ) ) = ( ( B logb A ) + ( E x. ( B logb C ) ) ) )

  proof
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    cA
    crp
    wcel
    #
    cC
    crp
    wcel
    #
    cE
    cr
    wcel
    #
    w3a
    #
    wa
    #
    cB
    cA
    cC
    cE
    ccxp
    co
    #
    cmul
    co
    clogb
    co
    #
    cB
    cA
    clogb
    co
    #
    cB
    @6
    clogb
    co
    #
    caddc
    co
    #
    @8
    cE
    cB
    cC
    clogb
    co
    cmul
    co
    #
    caddc
    co
    @4
    @0
    @1
    @6
    crp
    wcel
    #
    wa
    @7
    @10
    wceq
    @4
    @1
    @12
    @1
    @2
    @3
    simp1
    @2
    @3
    @12
    @1
    cC
    cE
    rpcxpcl
    3adant1
    jca
    cA
    cB
    @6
    relogbmul
    sylan2
    @5
    @9
    @11
    @8
    caddc
    @0
    @2
    @3
    @9
    @11
    wceq
    @1
    cB
    cC
    cE
    relogbreexp
    3adant3r1
    oveq2d
    eqtrd
end
