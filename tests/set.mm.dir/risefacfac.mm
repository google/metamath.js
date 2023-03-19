include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "caddc.mm"
include "cprod.mm"
include "crisefac.mm"
include "cfa.mm"
include "cfv.mm"
include "wa.mm"
include "1cnd.mm"
include "cc.mm"
include "elfznn.mm"
include "nncnd.mm"
include "adantl.mm"
include "pncan3d.mm"
include "prodeq2dv.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "risefacval2.mm"
include "mpan.mm"
include "fprodfac.mm"
include "3eqtr4d.mm"

theorem risefacfac
  let cN: class N
  let vk: setvar k


  assert |- ( N e. NN0 -> ( 1 RiseFac N ) = ( ! ` N ) )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    c1
    vk
    cv
    #
    c1
    cmin
    co
    caddc
    co
    #
    vk
    cprod
    #
    @1
    @2
    vk
    cprod
    c1
    cN
    crisefac
    co
    #
    cN
    cfa
    cfv
    @0
    @1
    @3
    @2
    vk
    @0
    @2
    @1
    wcel
    #
    wa
    #
    c1
    @2
    @7
    1cnd
    @6
    @2
    cc
    wcel
    @0
    @6
    @2
    @2
    cN
    elfznn
    nncnd
    adantl
    pncan3d
    prodeq2dv
    c1
    cc
    wcel
    @0
    @5
    @4
    wceq
    ax-1cn
    c1
    vk
    cN
    risefacval2
    mpan
    cN
    vk
    fprodfac
    3eqtr4d
end
