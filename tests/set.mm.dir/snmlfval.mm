include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmo.mm"
include "cfl.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cdiv.mm"
include "cn.mm"
include "oveq2.mm"
include "rabeq.mm"
include "syl.mm"
include "fveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem snmlfval
  let cA: class A
  let cB: class B
  let cR: class R
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cN: class N
  assume snmlff.f: |- F = ( n e. NN |-> ( ( # ` { k e. ( 1 ... n ) | ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = B } ) / n ) )

  disjoint A n
  disjoint B n
  disjoint k n
  disjoint N k
  disjoint N n
  disjoint R n
  assert |- ( N e. NN -> ( F ` N ) = ( ( # ` { k e. ( 1 ... N ) | ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = B } ) / N ) )

  proof
    vn
    cN
    cA
    cR
    vk
    cv
    cexp
    co
    cmul
    co
    cR
    cmo
    co
    cfl
    cfv
    cB
    wceq
    #
    vk
    c1
    vn
    cv
    #
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    @1
    cdiv
    co
    @0
    vk
    c1
    cN
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    cN
    cdiv
    co
    cn
    cF
    @1
    cN
    wceq
    #
    @4
    @7
    @1
    cN
    cdiv
    @8
    @3
    @6
    chash
    @8
    @2
    @5
    wceq
    @3
    @6
    wceq
    @1
    cN
    c1
    cfz
    oveq2
    @0
    vk
    @2
    @5
    rabeq
    syl
    fveq2d
    @8
    id
    oveq12d
    snmlff.f
    @7
    cN
    cdiv
    ovex
    fvmpt
end
