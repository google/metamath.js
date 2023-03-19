include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cim.mm"
include "c3.mm"
include "cexp.mm"
include "c6.mm"
include "cdiv.mm"
include "cmin.mm"
include "c4.mm"
include "cuz.mm"
include "cv.mm"
include "csu.mm"
include "caddc.mm"
include "resinval.mm"
include "c1.mm"
include "c2.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "efi4p.mm"
include "syl.mm"
include "fveq2d.mm"
include "1re.mm"
include "resqcl.mm"
include "rehalfcld.mm"
include "resubcl.mm"
include "sylancr.mm"
include "recnd.mm"
include "ax-icn.mm"
include "cn0.mm"
include "3nn0.mm"
include "reexpcl.mm"
include "mpan2.mm"
include "cc0.mm"
include "wne.mm"
include "6re.mm"
include "6pos.mm"
include "gt0ne0ii.mm"
include "redivcl.mm"
include "mp3an23.mm"
include "mpdan.mm"
include "mulcl.mm"
include "addcld.mm"
include "4nn0.mm"
include "eftlcl.mm"
include "sylancl.mm"
include "imaddd.mm"
include "crimd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"

theorem resin4p
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  assume efi4p.1: |- F = ( n e. NN0 |-> ( ( ( _i x. A ) ^ n ) / ( ! ` n ) ) )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint F k
  assert |- ( A e. RR -> ( sin ` A ) = ( ( A - ( ( A ^ 3 ) / 6 ) ) + ( Im ` sum_ k e. ( ZZ>= ` 4 ) ( F ` k ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cA
    csin
    cfv
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    cim
    cfv
    #
    cA
    cA
    c3
    cexp
    co
    #
    c6
    cdiv
    co
    #
    cmin
    co
    #
    c4
    cuz
    cfv
    vk
    cv
    cF
    cfv
    vk
    csu
    #
    cim
    cfv
    #
    caddc
    co
    #
    cA
    resinval
    @0
    @3
    c1
    cA
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    ci
    @6
    cmul
    co
    #
    caddc
    co
    #
    @7
    caddc
    co
    #
    cim
    cfv
    @14
    cim
    cfv
    #
    @8
    caddc
    co
    @9
    @0
    @2
    @15
    cim
    @0
    cA
    cc
    wcel
    #
    @2
    @15
    wceq
    cA
    recn
    #
    cA
    vk
    vn
    cF
    efi4p.1
    efi4p
    syl
    fveq2d
    @0
    @14
    @7
    @0
    @12
    @13
    @0
    @12
    @0
    c1
    cr
    wcel
    @11
    cr
    wcel
    @12
    cr
    wcel
    1re
    @0
    @10
    cA
    resqcl
    rehalfcld
    c1
    @11
    resubcl
    sylancr
    #
    recnd
    @0
    ci
    cc
    wcel
    #
    @6
    cc
    wcel
    @13
    cc
    wcel
    ax-icn
    @0
    @6
    @0
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    @0
    @4
    cr
    wcel
    #
    @21
    @0
    c3
    cn0
    wcel
    @22
    3nn0
    cA
    c3
    reexpcl
    mpan2
    @22
    c6
    cr
    wcel
    c6
    cc0
    wne
    @21
    6re
    c6
    6re
    6pos
    gt0ne0ii
    @4
    c6
    redivcl
    mp3an23
    syl
    cA
    @5
    resubcl
    mpdan
    #
    recnd
    ci
    @6
    mulcl
    sylancr
    addcld
    @0
    @1
    cc
    wcel
    #
    c4
    cn0
    wcel
    @7
    cc
    wcel
    @0
    @20
    @17
    @24
    ax-icn
    @18
    ci
    cA
    mulcl
    sylancr
    4nn0
    @1
    vk
    vn
    cF
    c4
    efi4p.1
    eftlcl
    sylancl
    imaddd
    @0
    @16
    @6
    @8
    caddc
    @0
    @12
    @6
    @19
    @23
    crimd
    oveq1d
    3eqtrd
    eqtrd
end
