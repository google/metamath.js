include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cneg.mm"
include "cmul.mm"
include "caddc.mm"
include "cmin.mm"
include "wceq.mm"
include "negcl.mm"
include "binom2.mm"
include "sylan2.mm"
include "negsub.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "mulneg2.mm"
include "oveq2d.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "eqtr2d.mm"
include "sqcl.mm"
include "adantr.mm"
include "negsubd.mm"
include "sqneg.mm"
include "adantl.mm"
include "oveq12d.mm"

theorem binom2sub
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A - B ) ^ 2 ) = ( ( ( A ^ 2 ) - ( 2 x. ( A x. B ) ) ) + ( B ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    c2
    cexp
    co
    #
    c2
    cA
    cB
    cneg
    #
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @4
    c2
    cexp
    co
    #
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    c2
    cexp
    co
    #
    @3
    c2
    cA
    cB
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    @2
    cA
    @4
    caddc
    co
    #
    c2
    cexp
    co
    #
    @9
    @11
    @1
    @0
    @4
    cc
    wcel
    @17
    @9
    wceq
    cB
    negcl
    cA
    @4
    binom2
    sylan2
    @2
    @16
    @10
    c2
    cexp
    cA
    cB
    negsub
    oveq1d
    eqtr3d
    @2
    @7
    @14
    @8
    @15
    caddc
    @2
    @3
    @13
    cneg
    #
    caddc
    co
    @7
    @14
    @2
    @18
    @6
    @3
    caddc
    @2
    @6
    c2
    @12
    cneg
    #
    cmul
    co
    #
    @18
    @2
    @5
    @19
    c2
    cmul
    cA
    cB
    mulneg2
    oveq2d
    @2
    c2
    cc
    wcel
    #
    @12
    cc
    wcel
    #
    @20
    @18
    wceq
    2cn
    cA
    cB
    mulcl
    #
    c2
    @12
    mulneg2
    sylancr
    eqtr2d
    oveq2d
    @2
    @3
    @13
    @0
    @3
    cc
    wcel
    @1
    cA
    sqcl
    adantr
    @2
    @21
    @22
    @13
    cc
    wcel
    2cn
    @23
    c2
    @12
    mulcl
    sylancr
    negsubd
    eqtr3d
    @1
    @8
    @15
    wceq
    @0
    cB
    sqneg
    adantl
    oveq12d
    eqtr3d
end
