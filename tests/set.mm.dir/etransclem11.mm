include "cn0.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "rabeqdv.mm"
include "fveq2.mm"
include "cbvsumv.mm"
include "fveq1.mm"
include "sumeq2ad.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "eqtrd.mm"
include "cbvmptv.mm"

theorem etransclem11
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cM: class M
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x

  disjoint M c
  disjoint M d
  disjoint M j
  disjoint M k
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint d j
  disjoint d k
  disjoint j k
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint j m
  disjoint M n
  disjoint c n
  disjoint d n
  disjoint k n
  disjoint m n
  disjoint k x
  assert |- ( n e. NN0 |-> { c e. ( ( 0 ... n ) ^m ( 0 ... M ) ) | sum_ j e. ( 0 ... M ) ( c ` j ) = n } ) = ( m e. NN0 |-> { d e. ( ( 0 ... m ) ^m ( 0 ... M ) ) | sum_ k e. ( 0 ... M ) ( d ` k ) = m } )

  proof
    vn
    vm
    cn0
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    vc
    cv
    #
    cfv
    #
    vj
    csu
    #
    vn
    cv
    #
    wceq
    #
    vc
    cc0
    @5
    cfz
    co
    #
    @0
    cmap
    co
    #
    crab
    #
    @0
    vk
    cv
    #
    vd
    cv
    #
    cfv
    #
    vk
    csu
    #
    vm
    cv
    #
    wceq
    #
    vd
    cc0
    @14
    cfz
    co
    #
    @0
    cmap
    co
    #
    crab
    #
    @5
    @14
    wceq
    #
    @9
    @6
    vc
    @17
    crab
    #
    @18
    @19
    @6
    vc
    @8
    @17
    @19
    @7
    @16
    @0
    cmap
    @5
    @14
    cc0
    cfz
    oveq2
    oveq1d
    rabeqdv
    @19
    @20
    @13
    @5
    wceq
    #
    vd
    @17
    crab
    @18
    @6
    @21
    vc
    vd
    @17
    @2
    @11
    wceq
    #
    @4
    @13
    @5
    @22
    @4
    @0
    @10
    @2
    cfv
    #
    vk
    csu
    @13
    @0
    @3
    @23
    vj
    vk
    @1
    @10
    @2
    fveq2
    cbvsumv
    @22
    @0
    @23
    @12
    vk
    @10
    @2
    @11
    fveq1
    sumeq2ad
    syl5eq
    eqeq1d
    cbvrabv
    @19
    @21
    @15
    vd
    @17
    @5
    @14
    @13
    eqeq2
    rabbidv
    syl5eq
    eqtrd
    cbvmptv
end
