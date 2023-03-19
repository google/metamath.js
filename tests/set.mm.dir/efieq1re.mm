include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cr.mm"
include "cim.mm"
include "cneg.mm"
include "cabs.mm"
include "cre.mm"
include "caddc.mm"
include "replim.mm"
include "oveq2d.mm"
include "recl.mm"
include "recnd.mm"
include "ax-icn.mm"
include "imcl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "adddi.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "ixi.mm"
include "oveq1i.mm"
include "mulass.mm"
include "mp3an12.mm"
include "syl.mm"
include "mulm1d.mm"
include "3eqtr3a.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "renegcld.mm"
include "efadd.mm"
include "eqeq1d.mm"
include "efcl.mm"
include "absmuld.mm"
include "absefi.mm"
include "reefcld.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "efgt0.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "mpan.mm"
include "sylc.mm"
include "absidd.mm"
include "oveq12d.mm"
include "mulid2d.mm"
include "3eqtrrd.mm"
include "fveq2.mm"
include "sylan9eq.mm"
include "ex.mm"
include "sylbid.mm"
include "negeq0d.mm"
include "reim0b.mm"
include "ef0.mm"
include "abs1.mm"
include "eqtr4i.mm"
include "eqeq2i.mm"
include "wb.mm"
include "reef11.mm"
include "sylancl.mm"
include "syl5bbr.mm"
include "3bitr4rd.mm"
include "sylibd.mm"
include "imp.mm"

theorem efieq1re
  let cA: class A


  assert |- ( ( A e. CC /\ ( exp ` ( _i x. A ) ) = 1 ) -> A e. RR )

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
    wceq
    #
    cA
    cr
    wcel
    #
    @0
    @3
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
    cabs
    cfv
    #
    wceq
    #
    @4
    @0
    @3
    ci
    cA
    cre
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    @7
    cmul
    co
    #
    c1
    wceq
    #
    @9
    @0
    @2
    @13
    c1
    @0
    @2
    @11
    @6
    caddc
    co
    #
    ce
    cfv
    #
    @13
    @0
    @1
    @15
    ce
    @0
    @1
    ci
    @10
    ci
    @5
    cmul
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @15
    @0
    cA
    @18
    ci
    cmul
    cA
    replim
    oveq2d
    @0
    @19
    @11
    ci
    @17
    cmul
    co
    #
    caddc
    co
    #
    @15
    @0
    @10
    cc
    wcel
    #
    @17
    cc
    wcel
    #
    @19
    @21
    wceq
    #
    @0
    @10
    cA
    recl
    #
    recnd
    #
    @0
    ci
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @23
    ax-icn
    @0
    @5
    cA
    imcl
    #
    recnd
    #
    ci
    @5
    mulcl
    sylancr
    @27
    @22
    @23
    @24
    ax-icn
    ci
    @10
    @17
    adddi
    mp3an1
    syl2anc
    @0
    @20
    @6
    @11
    caddc
    @0
    ci
    ci
    cmul
    co
    #
    @5
    cmul
    co
    #
    c1
    cneg
    #
    @5
    cmul
    co
    @20
    @6
    @31
    @33
    @5
    cmul
    ixi
    oveq1i
    @0
    @28
    @32
    @20
    wceq
    #
    @30
    @27
    @27
    @28
    @34
    ax-icn
    ax-icn
    ci
    ci
    @5
    mulass
    mp3an12
    syl
    @0
    @5
    @30
    mulm1d
    3eqtr3a
    oveq2d
    eqtrd
    eqtrd
    fveq2d
    @0
    @11
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @16
    @13
    wceq
    @0
    @27
    @22
    @35
    ax-icn
    @26
    ci
    @10
    mulcl
    sylancr
    #
    @0
    @6
    @0
    @5
    @29
    renegcld
    #
    recnd
    #
    @11
    @6
    efadd
    syl2anc
    eqtrd
    eqeq1d
    @0
    @14
    @9
    @0
    @14
    @7
    @13
    cabs
    cfv
    #
    @8
    @0
    @40
    @12
    cabs
    cfv
    #
    @7
    cabs
    cfv
    #
    cmul
    co
    c1
    @7
    cmul
    co
    @7
    @0
    @12
    @7
    @0
    @35
    @12
    cc
    wcel
    @37
    @11
    efcl
    syl
    @0
    @36
    @7
    cc
    wcel
    @39
    @6
    efcl
    syl
    #
    absmuld
    @0
    @41
    c1
    @42
    @7
    cmul
    @0
    @10
    cr
    wcel
    @41
    c1
    wceq
    @25
    @10
    absefi
    syl
    @0
    @7
    @0
    @6
    @38
    reefcld
    #
    @0
    @7
    cr
    wcel
    #
    cc0
    @7
    clt
    wbr
    #
    cc0
    @7
    cle
    wbr
    #
    @44
    @0
    @6
    cr
    wcel
    #
    @46
    @38
    @6
    efgt0
    syl
    cc0
    cr
    wcel
    #
    @45
    @46
    @47
    wi
    0re
    cc0
    @7
    ltle
    mpan
    sylc
    absidd
    oveq12d
    @0
    @7
    @43
    mulid2d
    3eqtrrd
    @13
    c1
    cabs
    fveq2
    sylan9eq
    ex
    sylbid
    @0
    @5
    cc0
    wceq
    @6
    cc0
    wceq
    #
    @4
    @9
    @0
    @5
    @30
    negeq0d
    cA
    reim0b
    @9
    @7
    cc0
    ce
    cfv
    #
    wceq
    #
    @0
    @50
    @51
    @8
    @7
    @51
    c1
    @8
    ef0
    abs1
    eqtr4i
    eqeq2i
    @0
    @48
    @49
    @52
    @50
    wb
    @38
    0re
    @6
    cc0
    reef11
    sylancl
    syl5bbr
    3bitr4rd
    sylibd
    imp
end
