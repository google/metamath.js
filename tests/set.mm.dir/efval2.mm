include "cc.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cdiv.mm"
include "csu.mm"
include "efval.mm"
include "eftval.mm"
include "sumeq2i.mm"
include "syl6eqr.mm"

theorem efval2
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  assume efcvg.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  assert |- ( A e. CC -> ( exp ` A ) = sum_ k e. NN0 ( F ` k ) )

  proof
    cA
    cc
    wcel
    cA
    ce
    cfv
    cn0
    cA
    vk
    cv
    #
    cexp
    co
    @0
    cfa
    cfv
    cdiv
    co
    #
    vk
    csu
    cn0
    @0
    cF
    cfv
    #
    vk
    csu
    cA
    vk
    efval
    cn0
    @2
    @1
    vk
    cA
    vn
    cF
    @0
    efcvg.1
    eftval
    sumeq2i
    syl6eqr
end
