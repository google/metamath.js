include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "csu.mm"
include "cc.mm"
include "ce.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "df-ef.mm"
include "sumex.mm"
include "fvmpt.mm"

theorem efval
  let cA: class A
  let vk: setvar k
  let vx: setvar x

  disjoint A k
  disjoint k x
  disjoint A x
  assert |- ( A e. CC -> ( exp ` A ) = sum_ k e. NN0 ( ( A ^ k ) / ( ! ` k ) ) )

  proof
    vx
    cA
    cn0
    vx
    cv
    #
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
    cn0
    cA
    @1
    cexp
    co
    #
    @3
    cdiv
    co
    #
    vk
    csu
    cc
    ce
    @0
    cA
    wceq
    #
    cn0
    @4
    @6
    vk
    @7
    @2
    @5
    @3
    cdiv
    @0
    cA
    @1
    cexp
    oveq1
    oveq1d
    sumeq2sdv
    vx
    vk
    df-ef
    cn0
    @6
    vk
    sumex
    fvmpt
end
