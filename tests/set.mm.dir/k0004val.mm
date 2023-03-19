include "c1.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cc0.mm"
include "cicc.mm"
include "cmap.mm"
include "crab.mm"
include "cn0.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "eqeq1d.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem k0004val
  let vt: setvar t
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vv: setvar v
  assume k0004.a: |- A = ( n e. NN0 |-> { t e. ( ( 0 [,] 1 ) ^m ( 1 ... ( n + 1 ) ) ) | sum_ k e. ( 1 ... ( n + 1 ) ) ( t ` k ) = 1 } )

  disjoint k n
  disjoint n t
  disjoint N k
  disjoint N t
  disjoint N n
  disjoint N v
  assert |- ( N e. NN0 -> ( A ` N ) = { t e. ( ( 0 [,] 1 ) ^m ( 1 ... ( N + 1 ) ) ) | sum_ k e. ( 1 ... ( N + 1 ) ) ( t ` k ) = 1 } )

  proof
    vn
    cN
    c1
    vn
    cv
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    vk
    cv
    vt
    cv
    cfv
    #
    vk
    csu
    #
    c1
    wceq
    #
    vt
    cc0
    c1
    cicc
    co
    #
    @2
    cmap
    co
    #
    crab
    c1
    cN
    c1
    caddc
    co
    #
    cfz
    co
    #
    @3
    vk
    csu
    #
    c1
    wceq
    #
    vt
    @6
    @9
    cmap
    co
    #
    crab
    cn0
    cA
    @0
    cN
    wceq
    #
    @5
    @11
    vt
    @7
    @12
    @13
    @2
    @9
    @6
    cmap
    @13
    @1
    @8
    c1
    cfz
    @0
    cN
    c1
    caddc
    oveq1
    oveq2d
    #
    oveq2d
    @13
    @4
    @10
    c1
    @13
    @2
    @9
    @3
    vk
    @14
    sumeq1d
    eqeq1d
    rabeqbidv
    k0004.a
    @11
    vt
    @12
    @6
    @9
    cmap
    ovex
    rabex
    fvmpt
end
