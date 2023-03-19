include "cc.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "caddc.mm"
include "cprod.mm"
include "crisefac.mm"
include "wceq.mm"
include "oveq1.mm"
include "prodeq2sdv.mm"
include "oveq2d.mm"
include "prodeq1d.mm"
include "df-risefac.mm"
include "prodex.mm"
include "ovmpt2.mm"

theorem risefacval
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  let vx: setvar x

  disjoint A k
  disjoint N k
  disjoint A n
  disjoint A x
  disjoint k n
  disjoint k x
  disjoint N n
  disjoint n x
  disjoint N x
  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( A RiseFac N ) = prod_ k e. ( 0 ... ( N - 1 ) ) ( A + k ) )

  proof
    vx
    vn
    cA
    cN
    cc
    cn0
    cc0
    vn
    cv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    vx
    cv
    #
    vk
    cv
    #
    caddc
    co
    #
    vk
    cprod
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    @4
    caddc
    co
    #
    vk
    cprod
    crisefac
    @2
    @8
    vk
    cprod
    @3
    cA
    wceq
    @2
    @5
    @8
    vk
    @3
    cA
    @4
    caddc
    oveq1
    prodeq2sdv
    @0
    cN
    wceq
    #
    @2
    @7
    @8
    vk
    @9
    @1
    @6
    cc0
    cfz
    @0
    cN
    c1
    cmin
    oveq1
    oveq2d
    prodeq1d
    vx
    vk
    vn
    df-risefac
    @7
    @8
    vk
    prodex
    ovmpt2
end
