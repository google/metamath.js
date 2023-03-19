include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "cfv.mm"
include "caddc.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "cim.mm"
include "0red.mm"
include "imcl.mm"
include "wa.mm"
include "cneg.mm"
include "cabs.mm"
include "cdiv.mm"
include "ccj.mm"
include "crp.mm"
include "cz.mm"
include "ax-icn.mm"
include "negcl.mm"
include "adantr.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "sqcld.mm"
include "subcl.mm"
include "sqrtcld.mm"
include "addcld.mm"
include "wne.mm"
include "asinlem.mm"
include "syl.mm"
include "absrpcld.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rprecred.mm"
include "cjcld.mm"
include "recld.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "wceq.mm"
include "imneg.mm"
include "le0neg2d.mm"
include "biimpa.mm"
include "eqbrtrd.mm"
include "asinlem3a.mm"
include "syl2anc.mm"
include "recjd.mm"
include "breqtrrd.mm"
include "mulge0d.mm"
include "recval.mm"
include "asinlem2.mm"
include "eqcomd.mm"
include "1cnd.mm"
include "simpl.mm"
include "sqcl.mm"
include "divmul3d.mm"
include "mpbird.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrec2d.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "remul2d.mm"
include "eqtrd.mm"
include "lecasei.mm"

theorem asinlem3
  let cA: class A


  assert |- ( A e. CC -> 0 <_ ( Re ` ( ( _i x. A ) + ( sqrt ` ( 1 - ( A ^ 2 ) ) ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cc0
    ci
    cA
    cmul
    co
    #
    c1
    cA
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    cre
    cfv
    #
    cle
    wbr
    cc0
    cA
    cim
    cfv
    #
    @0
    0red
    cA
    imcl
    #
    @0
    cc0
    @7
    cle
    wbr
    #
    wa
    #
    cc0
    c1
    ci
    cA
    cneg
    #
    cmul
    co
    #
    c1
    @11
    c2
    cexp
    co
    #
    cmin
    co
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @16
    ccj
    cfv
    #
    cre
    cfv
    #
    cmul
    co
    #
    @6
    cle
    @10
    @19
    @21
    @10
    @18
    @10
    @17
    crp
    wcel
    c2
    cz
    wcel
    @18
    crp
    wcel
    @10
    @16
    @10
    @12
    @15
    @10
    ci
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @12
    cc
    wcel
    ax-icn
    @0
    @24
    @9
    cA
    negcl
    adantr
    #
    ci
    @11
    mulcl
    sylancr
    @10
    @14
    @10
    c1
    cc
    wcel
    #
    @13
    cc
    wcel
    @14
    cc
    wcel
    ax-1cn
    @10
    @11
    @25
    sqcld
    c1
    @13
    subcl
    sylancr
    sqrtcld
    addcld
    #
    @10
    @24
    @16
    cc0
    wne
    #
    @25
    @11
    asinlem
    syl
    #
    absrpcld
    2z
    @17
    c2
    rpexpcl
    sylancl
    #
    rprecred
    #
    @10
    @20
    @10
    @16
    @27
    cjcld
    #
    recld
    @10
    @19
    @10
    @18
    @30
    rpreccld
    rpge0d
    @10
    cc0
    @16
    cre
    cfv
    #
    @21
    cle
    @10
    @24
    @11
    cim
    cfv
    #
    cc0
    cle
    wbr
    cc0
    @33
    cle
    wbr
    @25
    @10
    @34
    @7
    cneg
    #
    cc0
    cle
    @0
    @34
    @35
    wceq
    @9
    cA
    imneg
    adantr
    @0
    @9
    @35
    cc0
    cle
    wbr
    @0
    @7
    @8
    le0neg2d
    biimpa
    eqbrtrd
    @11
    asinlem3a
    syl2anc
    @10
    @16
    @27
    recjd
    breqtrrd
    mulge0d
    @10
    @6
    @19
    @20
    cmul
    co
    #
    cre
    cfv
    @22
    @10
    @5
    @36
    cre
    @10
    c1
    @16
    cdiv
    co
    #
    @20
    @18
    cdiv
    co
    #
    @5
    @36
    @10
    @16
    cc
    wcel
    @28
    @37
    @38
    wceq
    @27
    @29
    @16
    recval
    syl2anc
    @10
    @37
    @5
    wceq
    c1
    @5
    @16
    cmul
    co
    #
    wceq
    @10
    @39
    c1
    @0
    @39
    c1
    wceq
    @9
    cA
    asinlem2
    adantr
    eqcomd
    @10
    c1
    @5
    @16
    @10
    1cnd
    @10
    @1
    @4
    @10
    @23
    @0
    @1
    cc
    wcel
    ax-icn
    @0
    @9
    simpl
    ci
    cA
    mulcl
    sylancr
    @10
    @3
    @10
    @26
    @2
    cc
    wcel
    #
    @3
    cc
    wcel
    ax-1cn
    @0
    @40
    @9
    cA
    sqcl
    adantr
    c1
    @2
    subcl
    sylancr
    sqrtcld
    addcld
    @27
    @29
    divmul3d
    mpbird
    @10
    @20
    @18
    @32
    @10
    @18
    @30
    rpcnd
    @10
    @18
    @30
    rpne0d
    divrec2d
    3eqtr3d
    fveq2d
    @10
    @19
    @20
    @31
    @32
    remul2d
    eqtrd
    breqtrrd
    cA
    asinlem3a
    lecasei
end
