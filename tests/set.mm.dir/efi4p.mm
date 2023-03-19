include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c3.mm"
include "c6.mm"
include "c4.mm"
include "cuz.mm"
include "cv.mm"
include "csu.mm"
include "cmin.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "ef4p.mm"
include "syl.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "sylancr.mm"
include "sqcld.mm"
include "halfcld.mm"
include "cn0.mm"
include "3nn0.mm"
include "expcl.mm"
include "sylancl.mm"
include "cc0.mm"
include "wne.mm"
include "6cn.mm"
include "6re.mm"
include "6pos.mm"
include "gt0ne0ii.mm"
include "divcl.mm"
include "mp3an23.mm"
include "addassd.mm"
include "a1i.mm"
include "add4d.mm"
include "cneg.mm"
include "2nn0.mm"
include "mulexp.mm"
include "mp3an13.mm"
include "i2.mm"
include "oveq1i.mm"
include "sqcl.mm"
include "mulm1d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "2cn.mm"
include "2ne0.mm"
include "divneg.mm"
include "eqtr4d.mm"
include "oveq2d.mm"
include "negsub.mm"
include "eqtrd.mm"
include "i3.mm"
include "syl6eq.mm"
include "mpan2.mm"
include "wa.mm"
include "negicn.mm"
include "pm3.2i.mm"
include "divass.mm"
include "mulneg12.mm"
include "negcld.mm"
include "adddi.mm"
include "mp3an1.mm"
include "mpdan.mm"
include "3eqtr2d.mm"
include "oveq12d.mm"

theorem efi4p
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  assume efi4p.1: |- F = ( n e. NN0 |-> ( ( ( _i x. A ) ^ n ) / ( ! ` n ) ) )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint F k
  assert |- ( A e. CC -> ( exp ` ( _i x. A ) ) = ( ( ( 1 - ( ( A ^ 2 ) / 2 ) ) + ( _i x. ( A - ( ( A ^ 3 ) / 6 ) ) ) ) + sum_ k e. ( ZZ>= ` 4 ) ( F ` k ) ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    c1
    @1
    caddc
    co
    #
    @1
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    caddc
    co
    @1
    c3
    cexp
    co
    #
    c6
    cdiv
    co
    #
    caddc
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
    caddc
    co
    #
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
    cmul
    co
    #
    caddc
    co
    #
    @9
    caddc
    co
    @0
    @1
    cc
    wcel
    #
    @2
    @10
    wceq
    ci
    cc
    wcel
    #
    @0
    @19
    ax-icn
    ci
    cA
    mulcl
    mpan
    #
    @1
    vk
    vn
    cF
    efi4p.1
    ef4p
    syl
    @0
    @8
    @18
    @9
    caddc
    @0
    @8
    @3
    @5
    @7
    caddc
    co
    caddc
    co
    c1
    @5
    caddc
    co
    #
    @1
    @7
    caddc
    co
    #
    caddc
    co
    @18
    @0
    @3
    @5
    @7
    @0
    c1
    cc
    wcel
    #
    @19
    @3
    cc
    wcel
    ax-1cn
    @21
    c1
    @1
    addcl
    sylancr
    @0
    @4
    @0
    @1
    @21
    sqcld
    halfcld
    #
    @0
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @0
    @19
    c3
    cn0
    wcel
    #
    @26
    @21
    3nn0
    @1
    c3
    expcl
    sylancl
    @26
    c6
    cc
    wcel
    #
    c6
    cc0
    wne
    #
    @27
    6cn
    c6
    6re
    6pos
    gt0ne0ii
    #
    @6
    c6
    divcl
    mp3an23
    syl
    #
    addassd
    @0
    c1
    @1
    @5
    @7
    @24
    @0
    ax-1cn
    a1i
    @21
    @25
    @32
    add4d
    @0
    @22
    @13
    @23
    @17
    caddc
    @0
    @22
    c1
    @12
    cneg
    #
    caddc
    co
    #
    @13
    @0
    @5
    @33
    c1
    caddc
    @0
    @5
    @11
    cneg
    #
    c2
    cdiv
    co
    #
    @33
    @0
    @4
    @35
    c2
    cdiv
    @0
    @4
    ci
    c2
    cexp
    co
    #
    @11
    cmul
    co
    #
    c1
    cneg
    #
    @11
    cmul
    co
    #
    @35
    @20
    @0
    c2
    cn0
    wcel
    @4
    @38
    wceq
    ax-icn
    2nn0
    ci
    cA
    c2
    mulexp
    mp3an13
    @38
    @40
    wceq
    @0
    @37
    @39
    @11
    cmul
    i2
    oveq1i
    a1i
    @0
    @11
    cA
    sqcl
    #
    mulm1d
    3eqtrd
    oveq1d
    @0
    @11
    cc
    wcel
    #
    @33
    @36
    wceq
    #
    @41
    @42
    c2
    cc
    wcel
    c2
    cc0
    wne
    @43
    2cn
    2ne0
    @11
    c2
    divneg
    mp3an23
    syl
    eqtr4d
    oveq2d
    @0
    @24
    @12
    cc
    wcel
    @34
    @13
    wceq
    ax-1cn
    @0
    @11
    @41
    halfcld
    c1
    @12
    negsub
    sylancr
    eqtrd
    @0
    @23
    @1
    ci
    @15
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    ci
    cA
    @44
    caddc
    co
    #
    cmul
    co
    #
    @17
    @0
    @7
    @45
    @1
    caddc
    @0
    @7
    ci
    cneg
    #
    @14
    cmul
    co
    #
    c6
    cdiv
    co
    #
    @49
    @15
    cmul
    co
    #
    @45
    @0
    @6
    @50
    c6
    cdiv
    @0
    @6
    ci
    c3
    cexp
    co
    #
    @14
    cmul
    co
    #
    @50
    @20
    @0
    @28
    @6
    @54
    wceq
    ax-icn
    3nn0
    ci
    cA
    c3
    mulexp
    mp3an13
    @53
    @49
    @14
    cmul
    i3
    oveq1i
    syl6eq
    oveq1d
    @0
    @14
    cc
    wcel
    #
    @51
    @52
    wceq
    #
    @0
    @28
    @55
    3nn0
    cA
    c3
    expcl
    mpan2
    #
    @49
    cc
    wcel
    @55
    @29
    @30
    wa
    @56
    negicn
    @29
    @30
    6cn
    @31
    pm3.2i
    @49
    @14
    c6
    divass
    mp3an13
    syl
    @0
    @20
    @15
    cc
    wcel
    #
    @52
    @45
    wceq
    ax-icn
    @0
    @55
    @58
    @57
    @55
    @29
    @30
    @58
    6cn
    @31
    @14
    c6
    divcl
    mp3an23
    syl
    #
    ci
    @15
    mulneg12
    sylancr
    3eqtrd
    oveq2d
    @0
    @44
    cc
    wcel
    #
    @48
    @46
    wceq
    #
    @0
    @15
    @59
    negcld
    @20
    @0
    @60
    @61
    ax-icn
    ci
    cA
    @44
    adddi
    mp3an1
    mpdan
    @0
    @47
    @16
    ci
    cmul
    @0
    @58
    @47
    @16
    wceq
    @59
    cA
    @15
    negsub
    mpdan
    oveq2d
    3eqtr2d
    oveq12d
    3eqtrd
    oveq1d
    eqtrd
end
