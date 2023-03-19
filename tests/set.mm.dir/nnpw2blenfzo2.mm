include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cblen.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cfzo.mm"
include "wceq.mm"
include "caddc.mm"
include "wo.mm"
include "nnpw2blenfzo.mm"
include "elfzolborelfzop1.mm"
include "syl.mm"

theorem nnpw2blenfzo2
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( N = ( 2 ^ ( ( #b ` N ) - 1 ) ) \/ N e. ( ( ( 2 ^ ( ( #b ` N ) - 1 ) ) + 1 ) ..^ ( 2 ^ ( #b ` N ) ) ) ) )

  proof
    cN
    cn
    wcel
    cN
    c2
    cN
    cblen
    cfv
    #
    c1
    cmin
    co
    cexp
    co
    #
    c2
    @0
    cexp
    co
    #
    cfzo
    co
    wcel
    cN
    @1
    wceq
    cN
    @1
    c1
    caddc
    co
    @2
    cfzo
    co
    wcel
    wo
    cN
    nnpw2blenfzo
    cN
    @1
    @2
    elfzolborelfzop1
    syl
end
