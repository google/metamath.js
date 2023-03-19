include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cn0.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem eftval
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vk: setvar k
  assume eftval.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint A n
  disjoint N n
  disjoint k n
  disjoint A k
  disjoint F k
  assert |- ( N e. NN0 -> ( F ` N ) = ( ( A ^ N ) / ( ! ` N ) ) )

  proof
    vn
    cN
    cA
    vn
    cv
    #
    cexp
    co
    #
    @0
    cfa
    cfv
    #
    cdiv
    co
    cA
    cN
    cexp
    co
    #
    cN
    cfa
    cfv
    #
    cdiv
    co
    cn0
    cF
    @0
    cN
    wceq
    @1
    @3
    @2
    @4
    cdiv
    @0
    cN
    cA
    cexp
    oveq2
    @0
    cN
    cfa
    fveq2
    oveq12d
    eftval.1
    @3
    @4
    cdiv
    ovex
    fvmpt
end
