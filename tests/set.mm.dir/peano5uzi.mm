include "wcel.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "breq2.mm"
include "elrab.mm"
include "cmin.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "ax-mp.mm"
include "ax-1cn.mm"
include "subcli.mm"
include "npcan.mm"
include "sylancl.mm"
include "cn.mm"
include "subsub.mm"
include "mp3an23.mm"
include "syl.mm"
include "cn0.mm"
include "wb.mm"
include "znn0sub.mm"
include "mpan.mm"
include "biimpa.mm"
include "adantl.mm"
include "nn0p1nn.mm"
include "eqeltrd.mm"
include "simpl.mm"
include "wi.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "pncan3i.mm"
include "syl5eqel.mm"
include "rspccv.mm"
include "ad2antll.mm"
include "nncn.mm"
include "adantr.mm"
include "add32.mm"
include "sylibd.mm"
include "ex.mm"
include "a2d.mm"
include "nnind.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem peano5uzi
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  assume peano5uzi.1: |- N e. ZZ

  disjoint k x
  disjoint A k
  disjoint A x
  disjoint N k
  disjoint N x
  disjoint k n
  disjoint n x
  disjoint A n
  disjoint N n
  assert |- ( ( N e. A /\ A. x e. A ( x + 1 ) e. A ) -> { k e. ZZ | N <_ k } C_ A )

  proof
    cN
    cA
    wcel
    #
    vx
    cv
    #
    c1
    caddc
    co
    #
    cA
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vn
    cN
    vk
    cv
    #
    cle
    wbr
    #
    vk
    cz
    crab
    #
    cA
    vn
    cv
    #
    @8
    wcel
    @9
    cz
    wcel
    #
    cN
    @9
    cle
    wbr
    #
    wa
    #
    @5
    @9
    cA
    wcel
    #
    @7
    @11
    vk
    @9
    cz
    @6
    @9
    cN
    cle
    breq2
    elrab
    @5
    @12
    @13
    @5
    @12
    wa
    #
    @9
    cN
    c1
    cmin
    co
    #
    cmin
    co
    #
    @15
    caddc
    co
    #
    @9
    cA
    @14
    @9
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @17
    @9
    wceq
    @10
    @18
    @5
    @11
    @9
    zcn
    ad2antrl
    #
    cN
    c1
    cN
    cz
    wcel
    #
    cN
    cc
    wcel
    #
    peano5uzi.1
    cN
    zcn
    ax-mp
    #
    ax-1cn
    subcli
    #
    @9
    @15
    npcan
    sylancl
    @14
    @16
    cn
    wcel
    @5
    @17
    cA
    wcel
    #
    @14
    @16
    @9
    cN
    cmin
    co
    #
    c1
    caddc
    co
    #
    cn
    @14
    @18
    @16
    @27
    wceq
    #
    @20
    @18
    @22
    c1
    cc
    wcel
    #
    @28
    @23
    ax-1cn
    @9
    cN
    c1
    subsub
    mp3an23
    syl
    @14
    @26
    cn0
    wcel
    #
    @27
    cn
    wcel
    @12
    @30
    @5
    @10
    @11
    @30
    @21
    @10
    @11
    @30
    wb
    peano5uzi.1
    cN
    @9
    znn0sub
    mpan
    biimpa
    adantl
    @26
    nn0p1nn
    syl
    eqeltrd
    @5
    @12
    simpl
    @5
    @6
    @15
    caddc
    co
    #
    cA
    wcel
    #
    wi
    @5
    c1
    @15
    caddc
    co
    #
    cA
    wcel
    #
    wi
    @5
    @9
    @15
    caddc
    co
    #
    cA
    wcel
    #
    wi
    @5
    @9
    c1
    caddc
    co
    #
    @15
    caddc
    co
    #
    cA
    wcel
    #
    wi
    @5
    @25
    wi
    vk
    vn
    @16
    @6
    c1
    wceq
    #
    @32
    @34
    @5
    @40
    @31
    @33
    cA
    @6
    c1
    @15
    caddc
    oveq1
    eleq1d
    imbi2d
    @6
    @9
    wceq
    #
    @32
    @36
    @5
    @41
    @31
    @35
    cA
    @6
    @9
    @15
    caddc
    oveq1
    eleq1d
    imbi2d
    @6
    @37
    wceq
    #
    @32
    @39
    @5
    @42
    @31
    @38
    cA
    @6
    @37
    @15
    caddc
    oveq1
    eleq1d
    imbi2d
    @6
    @16
    wceq
    #
    @32
    @25
    @5
    @43
    @31
    @17
    cA
    @6
    @16
    @15
    caddc
    oveq1
    eleq1d
    imbi2d
    @5
    @33
    cN
    cA
    c1
    cN
    ax-1cn
    @23
    pncan3i
    @0
    @4
    simpl
    syl5eqel
    @9
    cn
    wcel
    #
    @5
    @36
    @39
    @44
    @5
    @36
    @39
    wi
    @44
    @5
    wa
    #
    @36
    @35
    c1
    caddc
    co
    #
    cA
    wcel
    #
    @39
    @4
    @36
    @47
    wi
    @44
    @0
    @3
    @47
    vx
    @35
    cA
    @1
    @35
    wceq
    @2
    @46
    cA
    @1
    @35
    c1
    caddc
    oveq1
    eleq1d
    rspccv
    ad2antll
    @45
    @46
    @38
    cA
    @45
    @18
    @46
    @38
    wceq
    #
    @44
    @18
    @5
    @9
    nncn
    adantr
    @18
    @19
    @29
    @48
    @24
    ax-1cn
    @9
    @15
    c1
    add32
    mp3an23
    syl
    eleq1d
    sylibd
    ex
    a2d
    nnind
    sylc
    eqeltrrd
    ex
    syl5bi
    ssrdv
end
