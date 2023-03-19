include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "cabs.mm"
include "c2.mm"
include "cexp.mm"
include "cre.mm"
include "cjadd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "cjcl.mm"
include "anim12i.mm"
include "muladd.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "addcl.mm"
include "absvalsq.mm"
include "syl.mm"
include "mulcom.mm"
include "oveqan12d.mm"
include "mulcl.mm"
include "sylan2.mm"
include "addcjd.mm"
include "cjmul.mm"
include "cjcj.mm"
include "adantl.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem sqabsadd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( abs ` ( A + B ) ) ^ 2 ) = ( ( ( ( abs ` A ) ^ 2 ) + ( ( abs ` B ) ^ 2 ) ) + ( 2 x. ( Re ` ( A x. ( * ` B ) ) ) ) ) )

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
    cB
    caddc
    co
    #
    @3
    ccj
    cfv
    #
    cmul
    co
    #
    cA
    cA
    ccj
    cfv
    #
    cmul
    co
    #
    cB
    ccj
    cfv
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    cA
    @8
    cmul
    co
    #
    @6
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
    @3
    cabs
    cfv
    c2
    cexp
    co
    #
    cA
    cabs
    cfv
    c2
    cexp
    co
    #
    cB
    cabs
    cfv
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @11
    cre
    cfv
    cmul
    co
    #
    caddc
    co
    @2
    @5
    @3
    @6
    @8
    caddc
    co
    #
    cmul
    co
    #
    @14
    @2
    @4
    @20
    @3
    cmul
    cA
    cB
    cjadd
    oveq2d
    @2
    @6
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    wa
    @21
    @14
    wceq
    @0
    @22
    @1
    @23
    cA
    cjcl
    cB
    cjcl
    #
    anim12i
    cA
    cB
    @6
    @8
    muladd
    mpdan
    eqtrd
    @2
    @3
    cc
    wcel
    @15
    @5
    wceq
    cA
    cB
    addcl
    @3
    absvalsq
    syl
    @2
    @18
    @10
    @19
    @13
    caddc
    @0
    @1
    @16
    @7
    @17
    @9
    caddc
    cA
    absvalsq
    @1
    @17
    cB
    @8
    cmul
    co
    #
    @9
    cB
    absvalsq
    @1
    @23
    @25
    @9
    wceq
    @24
    cB
    @8
    mulcom
    mpdan
    eqtrd
    oveqan12d
    @2
    @11
    @11
    ccj
    cfv
    #
    caddc
    co
    @19
    @13
    @2
    @11
    @1
    @0
    @23
    @11
    cc
    wcel
    @24
    cA
    @8
    mulcl
    sylan2
    addcjd
    @2
    @26
    @12
    @11
    caddc
    @2
    @26
    @6
    @8
    ccj
    cfv
    #
    cmul
    co
    #
    @12
    @1
    @0
    @23
    @26
    @28
    wceq
    @24
    cA
    @8
    cjmul
    sylan2
    @2
    @27
    cB
    @6
    cmul
    @1
    @27
    cB
    wceq
    @0
    cB
    cjcj
    adantl
    oveq2d
    eqtrd
    oveq2d
    eqtr3d
    oveq12d
    3eqtr4d
end
