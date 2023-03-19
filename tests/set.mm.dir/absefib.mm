include "cc.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cneg.mm"
include "ce.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cr.mm"
include "ef0.mm"
include "eqeq2i.mm"
include "wb.mm"
include "imcl.mm"
include "renegcld.mm"
include "0re.mm"
include "reef11.mm"
include "sylancl.mm"
include "syl5bbr.mm"
include "recnd.mm"
include "negeq0d.mm"
include "bitr4d.mm"
include "cre.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "absef.mm"
include "syl.mm"
include "caddc.mm"
include "replim.mm"
include "recl.mm"
include "sylancr.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "adddi.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "ixi.mm"
include "oveq1i.mm"
include "mulass.mm"
include "mp3an12.mm"
include "mulm1d.mm"
include "3eqtr3a.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "crred.mm"
include "eqeq1d.mm"
include "reim0b.mm"
include "3bitr4rd.mm"

theorem absefib
  let cA: class A


  assert |- ( A e. CC -> ( A e. RR <-> ( abs ` ( exp ` ( _i x. A ) ) ) = 1 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cim
    cfv
    #
    cneg
    #
    ce
    cfv
    #
    c1
    wceq
    #
    @1
    cc0
    wceq
    #
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    cabs
    cfv
    #
    c1
    wceq
    cA
    cr
    wcel
    @0
    @4
    @2
    cc0
    wceq
    #
    @5
    @4
    @3
    cc0
    ce
    cfv
    #
    wceq
    #
    @0
    @8
    @9
    c1
    @3
    ef0
    eqeq2i
    @0
    @2
    cr
    wcel
    cc0
    cr
    wcel
    @10
    @8
    wb
    @0
    @1
    cA
    imcl
    #
    renegcld
    #
    0re
    @2
    cc0
    reef11
    sylancl
    syl5bbr
    @0
    @1
    @0
    @1
    @11
    recnd
    #
    negeq0d
    bitr4d
    @0
    @7
    @3
    c1
    @0
    @7
    @6
    cre
    cfv
    #
    ce
    cfv
    #
    @3
    @0
    @6
    cc
    wcel
    #
    @7
    @15
    wceq
    ci
    cc
    wcel
    #
    @0
    @16
    ax-icn
    ci
    cA
    mulcl
    mpan
    @6
    absef
    syl
    @0
    @14
    @2
    ce
    @0
    @14
    @2
    ci
    cA
    cre
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cre
    cfv
    @2
    @0
    @6
    @20
    cre
    @0
    @6
    ci
    ci
    @1
    cmul
    co
    #
    @18
    caddc
    co
    #
    cmul
    co
    #
    @20
    @0
    cA
    @22
    ci
    cmul
    @0
    cA
    @18
    @21
    caddc
    co
    @22
    cA
    replim
    @0
    @18
    @21
    @0
    @18
    cA
    recl
    #
    recnd
    #
    @0
    @17
    @1
    cc
    wcel
    #
    @21
    cc
    wcel
    #
    ax-icn
    @13
    ci
    @1
    mulcl
    sylancr
    #
    addcomd
    eqtrd
    oveq2d
    @0
    @23
    ci
    @21
    cmul
    co
    #
    @19
    caddc
    co
    #
    @20
    @0
    @27
    @18
    cc
    wcel
    #
    @23
    @30
    wceq
    #
    @28
    @25
    @17
    @27
    @31
    @32
    ax-icn
    ci
    @21
    @18
    adddi
    mp3an1
    syl2anc
    @0
    @29
    @2
    @19
    caddc
    @0
    ci
    ci
    cmul
    co
    #
    @1
    cmul
    co
    #
    c1
    cneg
    #
    @1
    cmul
    co
    @29
    @2
    @33
    @35
    @1
    cmul
    ixi
    oveq1i
    @0
    @26
    @34
    @29
    wceq
    #
    @13
    @17
    @17
    @26
    @36
    ax-icn
    ax-icn
    ci
    ci
    @1
    mulass
    mp3an12
    syl
    @0
    @1
    @13
    mulm1d
    3eqtr3a
    oveq1d
    eqtrd
    eqtrd
    fveq2d
    @0
    @2
    @18
    @12
    @24
    crred
    eqtrd
    fveq2d
    eqtrd
    eqeq1d
    cA
    reim0b
    3bitr4rd
end
