include "ceu.mm"
include "c1.mm"
include "ce.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cdiv.mm"
include "csu.mm"
include "df-e.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "efval.mm"
include "ax-mp.mm"
include "cz.mm"
include "nn0z.mm"
include "1exp.mm"
include "syl.mm"
include "oveq1d.mm"
include "sumeq2i.mm"
include "3eqtri.mm"

theorem esum
  let vk: setvar k


  assert |- _e = sum_ k e. NN0 ( 1 / ( ! ` k ) )

  proof
    ceu
    c1
    ce
    cfv
    #
    cn0
    c1
    vk
    cv
    #
    cexp
    co
    #
    @1
    cfa
    cfv
    #
    cdiv
    co
    #
    vk
    csu
    #
    cn0
    c1
    @3
    cdiv
    co
    #
    vk
    csu
    df-e
    c1
    cc
    wcel
    @0
    @5
    wceq
    ax-1cn
    c1
    vk
    efval
    ax-mp
    cn0
    @4
    @6
    vk
    @1
    cn0
    wcel
    #
    @2
    c1
    @3
    cdiv
    @7
    @1
    cz
    wcel
    @2
    c1
    wceq
    @1
    nn0z
    @1
    1exp
    syl
    oveq1d
    sumeq2i
    3eqtri
end
