include "cn0.mm"
include "wcel.mm"
include "cv.mm"
include "cbc.mm"
include "co.mm"
include "cz.mm"
include "wral.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "cfz.mm"
include "wa.mm"
include "elfz1eq.mm"
include "adantl.mm"
include "oveq2.mm"
include "0nn0.mm"
include "bcn0.mm"
include "ax-mp.mm"
include "1nn0.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "syl.mm"
include "wn.mm"
include "bcval3.mm"
include "mp3an1.mm"
include "pm2.61dan.mm"
include "rgen.mm"
include "cbvralv.mm"
include "cmin.mm"
include "bcpasc.mm"
include "adantlr.mm"
include "rspccva.mm"
include "peano2zm.mm"
include "sylan2.mm"
include "nn0addcld.mm"
include "adantll.mm"
include "eqeltrrd.mm"
include "ralrimiva.mm"
include "ex.mm"
include "syl5bi.mm"
include "nn0ind.mm"
include "sylan.mm"

theorem bccl
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( N e. NN0 /\ K e. ZZ ) -> ( N _C K ) e. NN0 )

  proof
    cN
    cn0
    wcel
    cN
    vk
    cv
    #
    cbc
    co
    #
    cn0
    wcel
    #
    vk
    cz
    wral
    #
    cK
    cz
    wcel
    cN
    cK
    cbc
    co
    #
    cn0
    wcel
    #
    vm
    cv
    #
    @0
    cbc
    co
    #
    cn0
    wcel
    #
    vk
    cz
    wral
    cc0
    @0
    cbc
    co
    #
    cn0
    wcel
    #
    vk
    cz
    wral
    vn
    cv
    #
    @0
    cbc
    co
    #
    cn0
    wcel
    #
    vk
    cz
    wral
    #
    @11
    c1
    caddc
    co
    #
    @0
    cbc
    co
    #
    cn0
    wcel
    #
    vk
    cz
    wral
    #
    @3
    vm
    vn
    cN
    @6
    cc0
    wceq
    #
    @8
    @10
    vk
    cz
    @19
    @7
    @9
    cn0
    @6
    cc0
    @0
    cbc
    oveq1
    eleq1d
    ralbidv
    @6
    @11
    wceq
    #
    @8
    @13
    vk
    cz
    @20
    @7
    @12
    cn0
    @6
    @11
    @0
    cbc
    oveq1
    eleq1d
    ralbidv
    @6
    @15
    wceq
    #
    @8
    @17
    vk
    cz
    @21
    @7
    @16
    cn0
    @6
    @15
    @0
    cbc
    oveq1
    eleq1d
    ralbidv
    @6
    cN
    wceq
    #
    @8
    @2
    vk
    cz
    @22
    @7
    @1
    cn0
    @6
    cN
    @0
    cbc
    oveq1
    eleq1d
    ralbidv
    @10
    vk
    cz
    @0
    cz
    wcel
    #
    @0
    cc0
    cc0
    cfz
    co
    wcel
    #
    @10
    @23
    @24
    wa
    @0
    cc0
    wceq
    #
    @10
    @24
    @25
    @23
    @0
    cc0
    elfz1eq
    adantl
    @25
    @9
    cc0
    cc0
    cbc
    co
    #
    cn0
    @0
    cc0
    cc0
    cbc
    oveq2
    @26
    c1
    cn0
    cc0
    cn0
    wcel
    #
    @26
    c1
    wceq
    0nn0
    cc0
    bcn0
    ax-mp
    1nn0
    eqeltri
    syl6eqel
    syl
    @23
    @24
    wn
    #
    wa
    @9
    cc0
    cn0
    @27
    @23
    @28
    @9
    cc0
    wceq
    0nn0
    @0
    cc0
    bcval3
    mp3an1
    0nn0
    syl6eqel
    pm2.61dan
    rgen
    @14
    @11
    @6
    cbc
    co
    #
    cn0
    wcel
    #
    vm
    cz
    wral
    #
    @11
    cn0
    wcel
    #
    @18
    @13
    @30
    vk
    vm
    cz
    @0
    @6
    wceq
    @12
    @29
    cn0
    @0
    @6
    @11
    cbc
    oveq2
    eleq1d
    cbvralv
    @32
    @31
    @18
    @32
    @31
    wa
    #
    @17
    vk
    cz
    @33
    @23
    wa
    @12
    @11
    @0
    c1
    cmin
    co
    #
    cbc
    co
    #
    caddc
    co
    #
    @16
    cn0
    @32
    @23
    @36
    @16
    wceq
    @31
    @0
    @11
    bcpasc
    adantlr
    @31
    @23
    @36
    cn0
    wcel
    @32
    @31
    @23
    wa
    @12
    @35
    @30
    @13
    vm
    @0
    cz
    @6
    @0
    wceq
    @29
    @12
    cn0
    @6
    @0
    @11
    cbc
    oveq2
    eleq1d
    rspccva
    @23
    @31
    @34
    cz
    wcel
    @35
    cn0
    wcel
    #
    @0
    peano2zm
    @30
    @37
    vm
    @34
    cz
    @6
    @34
    wceq
    @29
    @35
    cn0
    @6
    @34
    @11
    cbc
    oveq2
    eleq1d
    rspccva
    sylan2
    nn0addcld
    adantll
    eqeltrrd
    ralrimiva
    ex
    syl5bi
    nn0ind
    @2
    @5
    vk
    cK
    cz
    @0
    cK
    wceq
    @1
    @4
    cn0
    @0
    cK
    cN
    cbc
    oveq2
    eleq1d
    rspccva
    sylan
end
