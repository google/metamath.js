include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "ctan.mm"
include "c2.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "c1.mm"
include "cmin.mm"
include "caddc.mm"
include "cdiv.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "atancl.mm"
include "2efiatan.mm"
include "oveq1d.mm"
include "2mulicn.mm"
include "a1i.mm"
include "cneg.mm"
include "atandm.mm"
include "simp1bi.mm"
include "ax-icn.mm"
include "addcl.mm"
include "sylancl.mm"
include "subneg.mm"
include "simp2bi.mm"
include "wb.mm"
include "negcli.mm"
include "wa.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "eqnetrrd.mm"
include "divcld.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "eqtrd.mm"
include "2muline0.mm"
include "divne0d.mm"
include "eqnetrd.mm"
include "tanval3.mm"
include "syl2anc.mm"
include "subsub4d.mm"
include "df-2.mm"
include "oveq2i.mm"
include "syl6eqr.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "divsubdird.mm"
include "mulneg12.mm"
include "negsub.mm"
include "negcld.mm"
include "pncan2.mm"
include "3eqtr3rd.mm"
include "oveq2d.mm"
include "subdid.mm"
include "3eqtr2rd.mm"
include "divcan4d.mm"
include "3eqtr3d.mm"
include "eqtr4d.mm"
include "mul12i.mm"
include "ixi.mm"
include "mulm1i.mm"
include "mulcomli.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "divassd.mm"
include "syl5eqr.mm"
include "oveq12d.mm"
include "2ne0.mm"
include "negne0i.mm"
include "divcan7d.mm"
include "divcan3d.mm"

theorem tanatan
  let cA: class A


  assert |- ( A e. dom arctan -> ( tan ` ( arctan ` A ) ) = A )

  proof
    cA
    catan
    cdm
    wcel
    #
    cA
    catan
    cfv
    #
    ctan
    cfv
    #
    c2
    ci
    @1
    cmul
    co
    cmul
    co
    ce
    cfv
    #
    c1
    cmin
    co
    #
    ci
    @3
    c1
    caddc
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cA
    @0
    @1
    cc
    wcel
    @5
    cc0
    wne
    @2
    @7
    wceq
    cA
    atancl
    @0
    @5
    c2
    ci
    cmul
    co
    #
    cA
    ci
    caddc
    co
    #
    cdiv
    co
    #
    cc0
    @0
    @5
    @10
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    @10
    @0
    @3
    @11
    c1
    caddc
    cA
    2efiatan
    #
    oveq1d
    @0
    @10
    cc
    wcel
    c1
    cc
    wcel
    #
    @12
    @10
    wceq
    @0
    @8
    @9
    @8
    cc
    wcel
    @0
    2mulicn
    a1i
    #
    @0
    cA
    cc
    wcel
    #
    ci
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @0
    @16
    cA
    ci
    cneg
    #
    wne
    #
    cA
    ci
    wne
    #
    cA
    atandm
    #
    simp1bi
    #
    ax-icn
    cA
    ci
    addcl
    sylancl
    #
    @0
    cA
    @19
    cmin
    co
    #
    @9
    cc0
    @0
    @16
    @17
    @25
    @9
    wceq
    @23
    ax-icn
    cA
    ci
    subneg
    sylancl
    @0
    @25
    cc0
    wne
    #
    @20
    @0
    @16
    @20
    @21
    @22
    simp2bi
    @0
    @16
    @19
    cc
    wcel
    #
    @26
    @20
    wb
    @23
    ci
    ax-icn
    negcli
    @16
    @27
    wa
    @25
    cc0
    cA
    @19
    cA
    @19
    subeq0
    necon3bid
    sylancl
    mpbird
    eqnetrrd
    #
    divcld
    #
    ax-1cn
    @10
    c1
    npcan
    sylancl
    eqtrd
    #
    @0
    @8
    @9
    @15
    @24
    @8
    cc0
    wne
    @0
    2muline0
    a1i
    @28
    divne0d
    eqnetrd
    @1
    tanval3
    syl2anc
    @0
    @7
    c2
    cneg
    #
    cA
    cmul
    co
    #
    @9
    cdiv
    co
    #
    @31
    @9
    cdiv
    co
    #
    cdiv
    co
    #
    cA
    @0
    @4
    @33
    @6
    @34
    cdiv
    @0
    @4
    @10
    c2
    cmin
    co
    #
    @33
    @0
    @4
    @11
    c1
    cmin
    co
    #
    @36
    @0
    @3
    @11
    c1
    cmin
    @13
    oveq1d
    @0
    @37
    @10
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @36
    @0
    @10
    c1
    c1
    @29
    @14
    @0
    ax-1cn
    a1i
    #
    @39
    subsub4d
    c2
    @38
    @10
    cmin
    df-2
    oveq2i
    syl6eqr
    eqtrd
    @0
    @8
    c2
    @9
    cmul
    co
    #
    cmin
    co
    #
    @9
    cdiv
    co
    @10
    @40
    @9
    cdiv
    co
    #
    cmin
    co
    @33
    @36
    @0
    @8
    @40
    @9
    @15
    @0
    c2
    cc
    wcel
    #
    @18
    @40
    cc
    wcel
    2cn
    @24
    c2
    @9
    mulcl
    sylancr
    @24
    @28
    divsubdird
    @0
    @41
    @32
    @9
    cdiv
    @0
    @32
    c2
    cA
    cneg
    #
    cmul
    co
    #
    c2
    ci
    @9
    cmin
    co
    #
    cmul
    co
    @41
    @0
    @43
    @16
    @32
    @45
    wceq
    2cn
    @23
    c2
    cA
    mulneg12
    sylancr
    @0
    @46
    @44
    c2
    cmul
    @0
    ci
    @44
    caddc
    co
    #
    ci
    cmin
    co
    #
    ci
    cA
    cmin
    co
    #
    ci
    cmin
    co
    @44
    @46
    @0
    @47
    @49
    ci
    cmin
    @0
    @17
    @16
    @47
    @49
    wceq
    ax-icn
    @23
    ci
    cA
    negsub
    sylancr
    oveq1d
    @0
    @17
    @44
    cc
    wcel
    @48
    @44
    wceq
    ax-icn
    @0
    cA
    @23
    negcld
    ci
    @44
    pncan2
    sylancr
    @0
    ci
    cA
    ci
    @17
    @0
    ax-icn
    a1i
    #
    @23
    @50
    subsub4d
    3eqtr3rd
    oveq2d
    @0
    c2
    ci
    @9
    @43
    @0
    2cn
    a1i
    #
    @50
    @24
    subdid
    3eqtr2rd
    oveq1d
    @0
    @42
    c2
    @10
    cmin
    @0
    c2
    @9
    @51
    @24
    @28
    divcan4d
    oveq2d
    3eqtr3d
    eqtr4d
    @0
    @6
    ci
    @10
    cmul
    co
    #
    @34
    @0
    @5
    @10
    ci
    cmul
    @30
    oveq2d
    @0
    @34
    ci
    @8
    cmul
    co
    #
    @9
    cdiv
    co
    @52
    @53
    @31
    @9
    cdiv
    @53
    c2
    ci
    ci
    cmul
    co
    #
    cmul
    co
    c2
    c1
    cneg
    #
    cmul
    co
    @31
    ci
    c2
    ci
    ax-icn
    2cn
    ax-icn
    mul12i
    @54
    @55
    c2
    cmul
    ixi
    oveq2i
    @55
    c2
    @31
    c1
    ax-1cn
    negcli
    2cn
    c2
    2cn
    mulm1i
    mulcomli
    3eqtri
    oveq1i
    @0
    ci
    @8
    @9
    @50
    @15
    @24
    @28
    divassd
    syl5eqr
    eqtr4d
    oveq12d
    @0
    @35
    @32
    @31
    cdiv
    co
    cA
    @0
    @32
    @31
    @9
    @0
    @31
    cc
    wcel
    #
    @16
    @32
    cc
    wcel
    c2
    2cn
    negcli
    #
    @23
    @31
    cA
    mulcl
    sylancr
    @56
    @0
    @57
    a1i
    #
    @24
    @31
    cc0
    wne
    @0
    c2
    2cn
    2ne0
    negne0i
    a1i
    #
    @28
    divcan7d
    @0
    cA
    @31
    @23
    @58
    @59
    divcan3d
    eqtrd
    eqtrd
    eqtrd
end
