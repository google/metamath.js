include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cgcd.mm"
include "wceq.mm"
include "mulgcd.mm"
include "3coml.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant1.mm"
include "nn0cn.mm"
include "3ad2ant3.mm"
include "mulcomd.mm"
include "3ad2ant2.mm"
include "oveq12d.mm"
include "gcdcl.mm"
include "3adant3.mm"
include "nn0cnd.mm"
include "3eqtr4d.mm"

theorem mulgcdr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ C e. NN0 ) -> ( ( A x. C ) gcd ( B x. C ) ) = ( ( A gcd B ) x. C ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cn0
    wcel
    #
    w3a
    #
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    cgcd
    co
    #
    cC
    cA
    cB
    cgcd
    co
    #
    cmul
    co
    #
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cgcd
    co
    @7
    cC
    cmul
    co
    @2
    @0
    @1
    @6
    @8
    wceq
    cC
    cA
    cB
    mulgcd
    3coml
    @3
    @9
    @4
    @10
    @5
    cgcd
    @3
    cA
    cC
    @0
    @1
    cA
    cc
    wcel
    @2
    cA
    zcn
    3ad2ant1
    @2
    @0
    cC
    cc
    wcel
    @1
    cC
    nn0cn
    3ad2ant3
    #
    mulcomd
    @3
    cB
    cC
    @1
    @0
    cB
    cc
    wcel
    @2
    cB
    zcn
    3ad2ant2
    @11
    mulcomd
    oveq12d
    @3
    @7
    cC
    @3
    @7
    @0
    @1
    @7
    cn0
    wcel
    @2
    cA
    cB
    gcdcl
    3adant3
    nn0cnd
    @11
    mulcomd
    3eqtr4d
end
