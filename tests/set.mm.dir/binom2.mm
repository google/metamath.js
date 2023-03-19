include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "0cn.mm"
include "elimel.mm"
include "binom2i.mm"
include "dedth2h.mm"

theorem binom2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A + B ) ^ 2 ) = ( ( ( A ^ 2 ) + ( 2 x. ( A x. B ) ) ) + ( B ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cA
    cB
    caddc
    co
    #
    c2
    cexp
    co
    #
    cA
    c2
    cexp
    co
    #
    c2
    cA
    cB
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    @0
    cA
    cc0
    cif
    #
    cB
    caddc
    co
    #
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    c2
    @10
    cB
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @8
    caddc
    co
    #
    wceq
    @10
    @1
    cB
    cc0
    cif
    #
    caddc
    co
    #
    c2
    cexp
    co
    #
    @13
    c2
    @10
    @18
    cmul
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    @18
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    cA
    cB
    cc0
    cc0
    cA
    @10
    wceq
    #
    @3
    @12
    @9
    @17
    @26
    @2
    @11
    c2
    cexp
    cA
    @10
    cB
    caddc
    oveq1
    oveq1d
    @26
    @7
    @16
    @8
    caddc
    @26
    @4
    @13
    @6
    @15
    caddc
    cA
    @10
    c2
    cexp
    oveq1
    @26
    @5
    @14
    c2
    cmul
    cA
    @10
    cB
    cmul
    oveq1
    oveq2d
    oveq12d
    oveq1d
    eqeq12d
    cB
    @18
    wceq
    #
    @12
    @20
    @17
    @25
    @27
    @11
    @19
    c2
    cexp
    cB
    @18
    @10
    caddc
    oveq2
    oveq1d
    @27
    @16
    @23
    @8
    @24
    caddc
    @27
    @15
    @22
    @13
    caddc
    @27
    @14
    @21
    c2
    cmul
    cB
    @18
    @10
    cmul
    oveq2
    oveq2d
    oveq2d
    cB
    @18
    c2
    cexp
    oveq1
    oveq12d
    eqeq12d
    @10
    @18
    cA
    cc0
    cc
    0cn
    elimel
    cB
    cc0
    cc
    0cn
    elimel
    binom2i
    dedth2h
end
