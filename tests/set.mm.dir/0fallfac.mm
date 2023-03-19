include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfallfac.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "caddc.mm"
include "cmul.mm"
include "cc.mm"
include "cn0.mm"
include "wceq.mm"
include "0cn.mm"
include "nnnn0.mm"
include "fallfacval.mm"
include "sylancr.mm"
include "cuz.mm"
include "cfv.mm"
include "nnm1nn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "subcl.mm"
include "adantl.mm"
include "oveq2.mm"
include "0m0e0.mm"
include "syl6eq.mm"
include "fprod1p.mm"
include "fzfid.mm"
include "fprodcl.mm"
include "mul02d.mm"
include "3eqtrd.mm"

theorem 0fallfac
  let cN: class N
  let vk: setvar k


  assert |- ( N e. NN -> ( 0 FallFac N ) = 0 )

  proof
    cN
    cn
    wcel
    #
    cc0
    cN
    cfallfac
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cc0
    vk
    cv
    #
    cmin
    co
    #
    vk
    cprod
    #
    cc0
    cc0
    c1
    caddc
    co
    #
    @2
    cfz
    co
    #
    @5
    vk
    cprod
    #
    cmul
    co
    cc0
    @0
    cc0
    cc
    wcel
    #
    cN
    cn0
    wcel
    @1
    @6
    wceq
    0cn
    cN
    nnnn0
    cc0
    vk
    cN
    fallfacval
    sylancr
    @0
    @5
    cc0
    vk
    cc0
    @2
    @0
    @2
    cn0
    cc0
    cuz
    cfv
    cN
    nnm1nn0
    nn0uz
    syl6eleq
    @4
    @3
    wcel
    #
    @5
    cc
    wcel
    #
    @0
    @11
    @10
    @4
    cc
    wcel
    #
    @12
    0cn
    @11
    @4
    @4
    cc0
    @2
    elfzelz
    zcnd
    cc0
    @4
    subcl
    #
    sylancr
    adantl
    @4
    cc0
    wceq
    @5
    cc0
    cc0
    cmin
    co
    cc0
    @4
    cc0
    cc0
    cmin
    oveq2
    0m0e0
    syl6eq
    fprod1p
    @0
    @9
    @0
    @8
    @5
    vk
    @0
    @7
    @2
    fzfid
    @4
    @8
    wcel
    #
    @12
    @0
    @15
    @10
    @13
    @12
    0cn
    @15
    @4
    @4
    @7
    @2
    elfzelz
    zcnd
    @14
    sylancr
    adantl
    fprodcl
    mul02d
    3eqtrd
end
