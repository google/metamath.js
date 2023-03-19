include "cn.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "cgcd.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "nncn.mm"
include "mulid1d.mm"
include "cabs.mm"
include "cfv.mm"
include "cz.mm"
include "nnz.mm"
include "gcdid.mm"
include "syl.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "eqtrd.mm"
include "wa.mm"
include "adantr.mm"
include "zmulcl.mm"
include "syl2an.mm"
include "1z.mm"
include "gcdaddm.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "cc.mm"
include "ax-1cn.mm"
include "adddi.mm"
include "mp3an3.mm"
include "mulcom.mm"
include "mpan2.mm"
include "eqtr4d.mm"
include "biimpd.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem gcdmultiple
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( M e. NN /\ N e. NN ) -> ( M gcd ( M x. N ) ) = M )

  proof
    cN
    cn
    wcel
    cM
    cn
    wcel
    #
    cM
    cM
    cN
    cmul
    co
    #
    cgcd
    co
    #
    cM
    wceq
    #
    @0
    cM
    cM
    vk
    cv
    #
    cmul
    co
    #
    cgcd
    co
    #
    cM
    wceq
    #
    wi
    @0
    cM
    cM
    c1
    cmul
    co
    #
    cgcd
    co
    #
    cM
    wceq
    #
    wi
    @0
    cM
    cM
    vn
    cv
    #
    cmul
    co
    #
    cgcd
    co
    #
    cM
    wceq
    #
    wi
    @0
    cM
    cM
    @11
    c1
    caddc
    co
    #
    cmul
    co
    #
    cgcd
    co
    #
    cM
    wceq
    #
    wi
    @0
    @3
    wi
    vk
    vn
    cN
    @4
    c1
    wceq
    #
    @7
    @10
    @0
    @19
    @6
    @9
    cM
    @19
    @5
    @8
    cM
    cgcd
    @4
    c1
    cM
    cmul
    oveq2
    oveq2d
    eqeq1d
    imbi2d
    vk
    vn
    weq
    #
    @7
    @14
    @0
    @20
    @6
    @13
    cM
    @20
    @5
    @12
    cM
    cgcd
    @4
    @11
    cM
    cmul
    oveq2
    oveq2d
    eqeq1d
    imbi2d
    @4
    @15
    wceq
    #
    @7
    @18
    @0
    @21
    @6
    @17
    cM
    @21
    @5
    @16
    cM
    cgcd
    @4
    @15
    cM
    cmul
    oveq2
    oveq2d
    eqeq1d
    imbi2d
    @4
    cN
    wceq
    #
    @7
    @3
    @0
    @22
    @6
    @2
    cM
    @22
    @5
    @1
    cM
    cgcd
    @4
    cN
    cM
    cmul
    oveq2
    oveq2d
    eqeq1d
    imbi2d
    @0
    @9
    cM
    cM
    cgcd
    co
    #
    cM
    @0
    @8
    cM
    cM
    cgcd
    @0
    cM
    cM
    nncn
    #
    mulid1d
    oveq2d
    @0
    @23
    cM
    cabs
    cfv
    #
    cM
    @0
    cM
    cz
    wcel
    #
    @23
    @25
    wceq
    cM
    nnz
    #
    cM
    gcdid
    syl
    @0
    cM
    cM
    nnre
    @0
    cM
    cM
    nnnn0
    nn0ge0d
    absidd
    eqtrd
    eqtrd
    @11
    cn
    wcel
    #
    @0
    @14
    @18
    @0
    @28
    @14
    @18
    wi
    @0
    @28
    wa
    #
    @14
    @18
    @29
    @13
    @17
    cM
    @29
    @13
    cM
    @12
    c1
    cM
    cmul
    co
    #
    caddc
    co
    #
    cgcd
    co
    #
    @17
    @29
    @26
    @12
    cz
    wcel
    #
    @13
    @32
    wceq
    #
    @0
    @26
    @28
    @27
    adantr
    @0
    @26
    @11
    cz
    wcel
    @33
    @28
    @27
    @11
    nnz
    cM
    @11
    zmulcl
    syl2an
    c1
    cz
    wcel
    @26
    @33
    @34
    1z
    c1
    cM
    @12
    gcdaddm
    mp3an1
    syl2anc
    @29
    @16
    @31
    cM
    cgcd
    @0
    cM
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @16
    @31
    wceq
    @28
    @24
    @11
    nncn
    @35
    @36
    wa
    #
    @16
    @12
    @8
    caddc
    co
    #
    @31
    @35
    @36
    c1
    cc
    wcel
    #
    @16
    @38
    wceq
    ax-1cn
    cM
    @11
    c1
    adddi
    mp3an3
    @37
    @8
    @30
    @12
    caddc
    @35
    @8
    @30
    wceq
    #
    @36
    @35
    @39
    @40
    ax-1cn
    cM
    c1
    mulcom
    mpan2
    adantr
    oveq2d
    eqtrd
    syl2an
    oveq2d
    eqtr4d
    eqeq1d
    biimpd
    expcom
    a2d
    nnind
    impcom
end
