include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cshi.mm"
include "cfv.mm"
include "wceq.mm"
include "subcl.mm"
include "3adant3.mm"
include "addcl.mm"
include "3adant2.mm"
include "shftval.mm"
include "syl2anc.mm"
include "pnncan.mm"
include "3com23.mm"
include "addcom.mm"
include "3adant1.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem shftval2
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC /\ C e. CC ) -> ( ( F shift ( A - B ) ) ` ( A + C ) ) = ( F ` ( B + C ) ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    cC
    caddc
    co
    #
    cF
    cA
    cB
    cmin
    co
    #
    cshi
    co
    cfv
    #
    @4
    @5
    cmin
    co
    #
    cF
    cfv
    #
    cB
    cC
    caddc
    co
    #
    cF
    cfv
    @3
    @5
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    @6
    @8
    wceq
    @0
    @1
    @10
    @2
    cA
    cB
    subcl
    3adant3
    @0
    @2
    @11
    @1
    cA
    cC
    addcl
    3adant2
    @5
    @4
    cF
    shftfval.1
    shftval
    syl2anc
    @3
    @7
    @9
    cF
    @3
    @7
    cC
    cB
    caddc
    co
    #
    @9
    @0
    @2
    @1
    @7
    @12
    wceq
    cA
    cC
    cB
    pnncan
    3com23
    @1
    @2
    @9
    @12
    wceq
    @0
    cB
    cC
    addcom
    3adant1
    eqtr4d
    fveq2d
    eqtrd
end
