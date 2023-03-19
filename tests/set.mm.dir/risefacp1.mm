include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cmul.mm"
include "crisefac.mm"
include "nn0cn.mm"
include "adantl.mm"
include "1cnd.mm"
include "pncand.mm"
include "oveq2d.mm"
include "prodeq1d.mm"
include "cuz.mm"
include "cfv.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "elfznn0.mm"
include "nn0cnd.mm"
include "addcl.mm"
include "sylan2.mm"
include "adantlr.mm"
include "oveq2.mm"
include "fprodm1.mm"
include "eqtrd.mm"
include "wceq.mm"
include "peano2nn0.mm"
include "risefacval.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"

theorem risefacp1
  let cA: class A
  let cN: class N
  let vk: setvar k


  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( A RiseFac ( N + 1 ) ) = ( ( A RiseFac N ) x. ( A + N ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cc0
    cN
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    cv
    #
    caddc
    co
    #
    vk
    cprod
    #
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    @7
    vk
    cprod
    #
    cA
    cN
    caddc
    co
    #
    cmul
    co
    #
    cA
    @3
    crisefac
    co
    #
    cA
    cN
    crisefac
    co
    #
    @10
    cmul
    co
    @2
    @8
    cc0
    cN
    cfz
    co
    #
    @7
    vk
    cprod
    @11
    @2
    @5
    @14
    @7
    vk
    @2
    @4
    cN
    cc0
    cfz
    @2
    cN
    c1
    @1
    cN
    cc
    wcel
    @0
    cN
    nn0cn
    adantl
    @2
    1cnd
    pncand
    oveq2d
    prodeq1d
    @2
    @7
    @10
    vk
    cc0
    cN
    @1
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @0
    @1
    @15
    cN
    elnn0uz
    biimpi
    adantl
    @0
    @6
    @14
    wcel
    #
    @7
    cc
    wcel
    #
    @1
    @16
    @0
    @6
    cc
    wcel
    @17
    @16
    @6
    @6
    cN
    elfznn0
    nn0cnd
    cA
    @6
    addcl
    sylan2
    adantlr
    @6
    cN
    cA
    caddc
    oveq2
    fprodm1
    eqtrd
    @1
    @0
    @3
    cn0
    wcel
    @12
    @8
    wceq
    cN
    peano2nn0
    cA
    vk
    @3
    risefacval
    sylan2
    @2
    @13
    @9
    @10
    cmul
    cA
    vk
    cN
    risefacval
    oveq1d
    3eqtr4d
end
