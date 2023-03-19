include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wn.mm"
include "cmul.mm"
include "wceq.mm"
include "cc.mm"
include "nncn.mm"
include "peano2cn.mm"
include "syl.mm"
include "2cn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan2d.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "cz.mm"
include "nnz.mm"
include "zneo.mm"
include "syl2an.mm"
include "expcom.mm"
include "necon2bd.mm"
include "syl5com.mm"
include "cv.mm"
include "wo.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "orbi12d.mm"
include "df-2.mm"
include "oveq1i.mm"
include "2div2e1.mm"
include "eqtr3i.mm"
include "1nn.mm"
include "eqeltri.mm"
include "orci.mm"
include "peano2nn.mm"
include "add1p1.mm"
include "wa.mm"
include "2cnne0.mm"
include "divdir.mm"
include "mp3an23.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "orim2d.mm"
include "orcom.mm"
include "syl6ib.mm"
include "nnind.mm"
include "ord.mm"
include "impbid.mm"

theorem nneo
  let cN: class N
  let vj: setvar j
  let vk: setvar k


  assert |- ( N e. NN -> ( ( N / 2 ) e. NN <-> -. ( ( N + 1 ) / 2 ) e. NN ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cn
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
    cn
    wcel
    #
    wn
    #
    @0
    c2
    @4
    cmul
    co
    #
    c2
    @1
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    @2
    @6
    @0
    @7
    @3
    @9
    @0
    @3
    c2
    @0
    cN
    cc
    wcel
    @3
    cc
    wcel
    cN
    nncn
    #
    cN
    peano2cn
    syl
    c2
    cc
    wcel
    #
    @0
    2cn
    a1i
    #
    c2
    cc0
    wne
    #
    @0
    2ne0
    a1i
    #
    divcan2d
    @0
    @8
    cN
    c1
    caddc
    @0
    cN
    c2
    @10
    @12
    @14
    divcan2d
    oveq1d
    eqtr4d
    @2
    @5
    @7
    @9
    @5
    @2
    @7
    @9
    wne
    #
    @5
    @4
    cz
    wcel
    @1
    cz
    wcel
    @15
    @2
    @4
    nnz
    @1
    nnz
    @4
    @1
    zneo
    syl2an
    expcom
    necon2bd
    syl5com
    @0
    @5
    @2
    vj
    cv
    #
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
    @16
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wo
    c1
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
    c1
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wo
    vk
    cv
    #
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
    @27
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wo
    #
    @28
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
    @30
    wo
    #
    @5
    @2
    wo
    vj
    vk
    cN
    @16
    c1
    wceq
    #
    @19
    @24
    @21
    @26
    @38
    @18
    @23
    cn
    @38
    @17
    @22
    c2
    cdiv
    @16
    c1
    c1
    caddc
    oveq1
    oveq1d
    eleq1d
    @38
    @20
    @25
    cn
    @16
    c1
    c2
    cdiv
    oveq1
    eleq1d
    orbi12d
    @16
    @27
    wceq
    #
    @19
    @30
    @21
    @32
    @39
    @18
    @29
    cn
    @39
    @17
    @28
    c2
    cdiv
    @16
    @27
    c1
    caddc
    oveq1
    oveq1d
    eleq1d
    @39
    @20
    @31
    cn
    @16
    @27
    c2
    cdiv
    oveq1
    eleq1d
    orbi12d
    @16
    @28
    wceq
    #
    @19
    @36
    @21
    @30
    @40
    @18
    @35
    cn
    @40
    @17
    @34
    c2
    cdiv
    @16
    @28
    c1
    caddc
    oveq1
    oveq1d
    eleq1d
    @40
    @20
    @29
    cn
    @16
    @28
    c2
    cdiv
    oveq1
    eleq1d
    orbi12d
    @16
    cN
    wceq
    #
    @19
    @5
    @21
    @2
    @41
    @18
    @4
    cn
    @41
    @17
    @3
    c2
    cdiv
    @16
    cN
    c1
    caddc
    oveq1
    oveq1d
    eleq1d
    @41
    @20
    @1
    cn
    @16
    cN
    c2
    cdiv
    oveq1
    eleq1d
    orbi12d
    @24
    @26
    @23
    c1
    cn
    c2
    c2
    cdiv
    co
    #
    @23
    c1
    c2
    @22
    c2
    cdiv
    df-2
    oveq1i
    2div2e1
    eqtr3i
    1nn
    eqeltri
    orci
    @27
    cn
    wcel
    #
    @33
    @30
    @36
    wo
    @37
    @43
    @32
    @36
    @30
    @32
    @36
    @43
    @31
    c1
    caddc
    co
    #
    cn
    wcel
    @31
    peano2nn
    @43
    @35
    @44
    cn
    @43
    @27
    cc
    wcel
    #
    @35
    @44
    wceq
    @27
    nncn
    @45
    @35
    @27
    c2
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @44
    @45
    @34
    @46
    c2
    cdiv
    @27
    add1p1
    oveq1d
    @45
    @47
    @31
    @42
    caddc
    co
    #
    @44
    @45
    @11
    @11
    @13
    wa
    @47
    @48
    wceq
    2cn
    2cnne0
    @27
    c2
    c2
    divdir
    mp3an23
    @42
    c1
    @31
    caddc
    2div2e1
    oveq2i
    syl6eq
    eqtrd
    syl
    eleq1d
    syl5ibr
    orim2d
    @30
    @36
    orcom
    syl6ib
    nnind
    ord
    impbid
end
