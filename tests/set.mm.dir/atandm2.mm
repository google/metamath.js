include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cc.mm"
include "ci.mm"
include "cneg.mm"
include "wne.mm"
include "w3a.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "caddc.mm"
include "atandm.mm"
include "wa.mm"
include "3anass.mm"
include "wceq.mm"
include "wb.mm"
include "ax-1cn.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "subeq0.mm"
include "sylancr.mm"
include "mulneg2i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "3eqtri.mm"
include "eqeq2i.mm"
include "eqcom.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "id.mm"
include "negcli.mm"
include "a1i.mm"
include "ine0.mm"
include "mulcand.mm"
include "bitrd.mm"
include "necon3bid.mm"
include "addcom.mm"
include "subneg.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem atandm2
  let cA: class A


  assert |- ( A e. dom arctan <-> ( A e. CC /\ ( 1 - ( _i x. A ) ) =/= 0 /\ ( 1 + ( _i x. A ) ) =/= 0 ) )

  proof
    cA
    catan
    cdm
    wcel
    cA
    cc
    wcel
    #
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
    w3a
    #
    @0
    c1
    ci
    cA
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wne
    #
    c1
    @5
    caddc
    co
    #
    cc0
    wne
    #
    w3a
    #
    cA
    atandm
    @10
    @0
    @7
    @9
    wa
    #
    wa
    #
    @4
    @0
    @7
    @9
    3anass
    @12
    @0
    @2
    @3
    wa
    #
    wa
    @4
    @0
    @11
    @13
    @0
    @7
    @2
    @9
    @3
    @0
    @6
    cc0
    cA
    @1
    @0
    @6
    cc0
    wceq
    #
    @5
    ci
    @1
    cmul
    co
    #
    wceq
    #
    cA
    @1
    wceq
    @0
    @14
    c1
    @5
    wceq
    #
    @16
    @0
    c1
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @14
    @17
    wb
    ax-1cn
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
    c1
    @5
    subeq0
    sylancr
    @16
    @5
    c1
    wceq
    @17
    @15
    c1
    @5
    @15
    ci
    ci
    cmul
    co
    #
    cneg
    c1
    cneg
    #
    cneg
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg2i
    @22
    @23
    ixi
    negeqi
    negneg1e1
    3eqtri
    eqeq2i
    @5
    c1
    eqcom
    bitri
    syl6bbr
    @0
    cA
    @1
    ci
    @0
    id
    #
    @1
    cc
    wcel
    @0
    ci
    ax-icn
    negcli
    a1i
    @20
    @0
    ax-icn
    a1i
    #
    ci
    cc0
    wne
    @0
    ine0
    a1i
    #
    mulcand
    bitrd
    necon3bid
    @0
    @8
    cc0
    cA
    ci
    @0
    @8
    cc0
    wceq
    #
    @5
    @22
    wceq
    #
    cA
    ci
    wceq
    @0
    @27
    @5
    @23
    wceq
    #
    @28
    @0
    @27
    @5
    @23
    cmin
    co
    #
    cc0
    wceq
    #
    @29
    @0
    @8
    @30
    cc0
    @0
    @8
    @5
    c1
    caddc
    co
    #
    @30
    @0
    @18
    @19
    @8
    @32
    wceq
    ax-1cn
    @21
    c1
    @5
    addcom
    sylancr
    @0
    @19
    @18
    @30
    @32
    wceq
    @21
    ax-1cn
    @5
    c1
    subneg
    sylancl
    eqtr4d
    eqeq1d
    @0
    @19
    @23
    cc
    wcel
    @31
    @29
    wb
    @21
    c1
    ax-1cn
    negcli
    @5
    @23
    subeq0
    sylancl
    bitrd
    @22
    @23
    @5
    ixi
    eqeq2i
    syl6bbr
    @0
    cA
    ci
    ci
    @24
    @25
    @25
    @26
    mulcand
    bitrd
    necon3bid
    anbi12d
    pm5.32i
    @0
    @2
    @3
    3anass
    bitr4i
    bitri
    bitr4i
end
