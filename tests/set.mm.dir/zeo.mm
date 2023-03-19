include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cr.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "cneg.mm"
include "w3o.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "elz.mm"
include "oveq1.mm"
include "2cn.mm"
include "2ne0.mm"
include "div0i.mm"
include "0z.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "pm2.24d.mm"
include "adantl.mm"
include "nnz.mm"
include "con3i.mm"
include "nneo.mm"
include "biimprd.mm"
include "con1d.mm"
include "syl56.mm"
include "cc.mm"
include "recn.mm"
include "wne.mm"
include "divneg.mm"
include "mp3an23.mm"
include "syl.mm"
include "eleq1d.mm"
include "nnnegz.mm"
include "syl6bir.mm"
include "halfcld.mm"
include "negnegd.mm"
include "sylibd.mm"
include "adantr.mm"
include "con3d.mm"
include "cmin.mm"
include "peano2zm.mm"
include "ax-1cn.mm"
include "negsubdi2i.mm"
include "2m1e1.mm"
include "eqtr2i.mm"
include "subcli.mm"
include "negcon2i.mm"
include "mpbi.mm"
include "oveq2i.mm"
include "negcl.mm"
include "addsubass.mm"
include "negdi.mm"
include "mpan2.mm"
include "3eqtr4a.mm"
include "oveq1d.mm"
include "peano2cn.mm"
include "2cnne0.mm"
include "divsubdir.mm"
include "2div2e1.mm"
include "eqcomi.mm"
include "syl6reqr.mm"
include "3eqtr4d.mm"
include "syl5ib.mm"
include "znegcl.mm"
include "syl6.mm"
include "peano2re.mm"
include "recnd.mm"
include "syl5.mm"
include "sylan9r.mm"
include "syld.mm"
include "3jaodan.mm"
include "sylbi.mm"
include "orrd.mm"

theorem zeo
  let cN: class N


  assert |- ( N e. ZZ -> ( ( N / 2 ) e. ZZ \/ ( ( N + 1 ) / 2 ) e. ZZ ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    @0
    cN
    cr
    wcel
    #
    cN
    cc0
    wceq
    #
    cN
    cn
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    w3o
    wa
    @2
    wn
    #
    @5
    wi
    #
    cN
    elz
    @6
    @7
    @12
    @8
    @10
    @7
    @12
    @6
    @7
    @2
    @5
    @7
    @1
    cc0
    c2
    cdiv
    co
    #
    cz
    cN
    cc0
    c2
    cdiv
    oveq1
    @13
    cc0
    cz
    c2
    2cn
    2ne0
    div0i
    0z
    eqeltri
    syl6eqel
    pm2.24d
    adantl
    @8
    @12
    @6
    @11
    @1
    cn
    wcel
    #
    wn
    @8
    @4
    cn
    wcel
    #
    @5
    @14
    @2
    @1
    nnz
    con3i
    @8
    @15
    @14
    @8
    @14
    @15
    wn
    cN
    nneo
    biimprd
    con1d
    @4
    nnz
    syl56
    adantl
    @6
    @10
    wa
    #
    @11
    @9
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wn
    #
    @5
    @16
    @18
    @2
    @6
    @18
    @2
    wi
    @10
    @6
    @18
    @1
    cneg
    #
    cneg
    #
    cz
    wcel
    #
    @2
    @6
    @18
    @20
    cn
    wcel
    @22
    @6
    @20
    @17
    cn
    @6
    cN
    cc
    wcel
    #
    @20
    @17
    wceq
    #
    cN
    recn
    #
    @23
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    @24
    2cn
    2ne0
    cN
    c2
    divneg
    mp3an23
    syl
    eleq1d
    @20
    nnnegz
    syl6bir
    @6
    @21
    @1
    cz
    @6
    @1
    @6
    cN
    @25
    halfcld
    negnegd
    eleq1d
    sylibd
    adantr
    con3d
    @10
    @19
    @9
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    @6
    @5
    @10
    @30
    @18
    @10
    @18
    @30
    wn
    @9
    nneo
    biimprd
    con1d
    @30
    @29
    cz
    wcel
    #
    @6
    @5
    @29
    nnz
    @6
    @31
    @4
    cneg
    #
    cneg
    #
    cz
    wcel
    #
    @5
    @6
    @31
    @32
    cz
    wcel
    #
    @34
    @31
    @29
    c1
    cmin
    co
    #
    cz
    wcel
    @6
    @35
    @29
    peano2zm
    @6
    @36
    @32
    cz
    @6
    @23
    @36
    @32
    wceq
    @25
    @23
    @28
    c2
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @3
    cneg
    #
    c2
    cdiv
    co
    #
    @36
    @32
    @23
    @37
    @39
    c2
    cdiv
    @23
    @9
    c1
    c2
    cmin
    co
    #
    caddc
    co
    #
    @9
    c1
    cneg
    #
    caddc
    co
    #
    @37
    @39
    @41
    @43
    @9
    caddc
    c1
    @41
    cneg
    #
    wceq
    @41
    @43
    wceq
    @45
    c2
    c1
    cmin
    co
    c1
    c1
    c2
    ax-1cn
    2cn
    negsubdi2i
    2m1e1
    eqtr2i
    c1
    @41
    ax-1cn
    c1
    c2
    ax-1cn
    2cn
    subcli
    negcon2i
    mpbi
    oveq2i
    @23
    @9
    cc
    wcel
    #
    @37
    @42
    wceq
    #
    cN
    negcl
    #
    @46
    c1
    cc
    wcel
    #
    @26
    @47
    ax-1cn
    2cn
    @9
    c1
    c2
    addsubass
    mp3an23
    syl
    @23
    @49
    @39
    @44
    wceq
    ax-1cn
    cN
    c1
    negdi
    mpan2
    3eqtr4a
    oveq1d
    @23
    @38
    @29
    c2
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @36
    @23
    @28
    cc
    wcel
    #
    @38
    @51
    wceq
    #
    @23
    @46
    @52
    @48
    @9
    peano2cn
    syl
    @52
    @26
    @26
    @27
    wa
    @53
    2cn
    2cnne0
    @28
    c2
    c2
    divsubdir
    mp3an23
    syl
    c1
    @50
    @29
    cmin
    @50
    c1
    2div2e1
    eqcomi
    oveq2i
    syl6reqr
    @23
    @3
    cc
    wcel
    #
    @32
    @40
    wceq
    #
    cN
    peano2cn
    @54
    @26
    @27
    @55
    2cn
    2ne0
    @3
    c2
    divneg
    mp3an23
    syl
    3eqtr4d
    syl
    eleq1d
    syl5ib
    @32
    znegcl
    syl6
    @6
    @33
    @4
    cz
    @6
    @4
    @6
    @3
    @6
    @3
    cN
    peano2re
    recnd
    halfcld
    negnegd
    eleq1d
    sylibd
    syl5
    sylan9r
    syld
    3jaodan
    sylbi
    orrd
end
