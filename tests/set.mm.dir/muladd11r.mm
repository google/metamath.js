include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "simpl.mm"
include "1cnd.mm"
include "addcomd.mm"
include "simpr.mm"
include "oveq12d.mm"
include "muladd11.mm"
include "mulcl.mm"
include "addcld.mm"
include "addassd.mm"
include "addcl.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem muladd11r
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( A + 1 ) x. ( B + 1 ) ) = ( ( ( A x. B ) + ( A + B ) ) + 1 ) )

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
    c1
    caddc
    co
    #
    cB
    c1
    caddc
    co
    #
    cmul
    co
    c1
    cA
    caddc
    co
    #
    c1
    cB
    caddc
    co
    #
    cmul
    co
    @5
    cB
    cA
    cB
    cmul
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @7
    cA
    cB
    caddc
    co
    #
    caddc
    co
    #
    c1
    caddc
    co
    #
    @2
    @3
    @5
    @4
    @6
    cmul
    @2
    cA
    c1
    @0
    @1
    simpl
    #
    @2
    1cnd
    #
    addcomd
    @2
    cB
    c1
    @0
    @1
    simpr
    #
    @14
    addcomd
    oveq12d
    cA
    cB
    muladd11
    @2
    @9
    c1
    cA
    @8
    caddc
    co
    #
    caddc
    co
    @16
    c1
    caddc
    co
    @12
    @2
    c1
    cA
    @8
    @14
    @13
    @2
    cB
    @7
    @15
    cA
    cB
    mulcl
    #
    addcld
    #
    addassd
    @2
    c1
    @16
    @14
    @2
    cA
    @8
    @13
    @18
    addcld
    addcomd
    @2
    @16
    @11
    c1
    caddc
    @2
    @10
    @7
    caddc
    co
    @16
    @11
    @2
    cA
    cB
    @7
    @13
    @15
    @17
    addassd
    @2
    @10
    @7
    cA
    cB
    addcl
    @17
    addcomd
    eqtr3d
    oveq1d
    3eqtrd
    3eqtrd
end
