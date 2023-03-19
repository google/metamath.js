include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "clogb.mm"
include "co.mm"
include "cmin.mm"
include "cfl.mm"
include "cfv.mm"
include "cexp.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "caddc.mm"
include "cr.mm"
include "cuz.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "relogbzcl.mm"
include "mpan.mm"
include "renegcld.mm"
include "flltp1.mm"
include "syl.mm"
include "wceq.mm"
include "1z.mm"
include "fladdz.mm"
include "sylancl.mm"
include "cc.mm"
include "recnd.mm"
include "ax-1cn.mm"
include "wa.mm"
include "negsubdi.mm"
include "negsubdi2.mm"
include "eqtr3d.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "wb.mm"
include "a1i.mm"
include "2rp.mm"
include "1red.mm"
include "resubcld.mm"
include "flcld.mm"
include "rpexpcld.mm"
include "rpreccld.mm"
include "id.mm"
include "logblt.mm"
include "syl3anc.mm"
include "logbrec.mm"
include "syl2anc.mm"
include "breq1d.mm"
include "ltnegcon1.mm"
include "3bitrd.mm"
include "nnlogbexp.mm"
include "breq2d.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem dya2ub
  let cR: class R


  assert |- ( R e. RR+ -> ( 1 / ( 2 ^ ( |_ ` ( 1 - ( 2 logb R ) ) ) ) ) < R )

  proof
    cR
    crp
    wcel
    #
    c1
    c2
    c1
    c2
    cR
    clogb
    co
    #
    cmin
    co
    #
    cfl
    cfv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cR
    clt
    wbr
    #
    @1
    cneg
    #
    @3
    clt
    wbr
    #
    @0
    @7
    @7
    cfl
    cfv
    c1
    caddc
    co
    #
    @3
    clt
    @0
    @7
    cr
    wcel
    #
    @7
    @9
    clt
    wbr
    @0
    @1
    c2
    c2
    cuz
    cfv
    wcel
    #
    @0
    @1
    cr
    wcel
    #
    c2
    cz
    wcel
    @11
    2z
    c2
    uzid
    ax-mp
    #
    c2
    cR
    relogbzcl
    mpan
    #
    renegcld
    #
    @7
    flltp1
    syl
    @0
    @7
    c1
    caddc
    co
    #
    cfl
    cfv
    #
    @9
    @3
    @0
    @10
    c1
    cz
    wcel
    @17
    @9
    wceq
    @15
    1z
    @7
    c1
    fladdz
    sylancl
    @0
    @16
    @2
    cfl
    @0
    @1
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @16
    @2
    wceq
    @0
    @1
    @14
    recnd
    ax-1cn
    @18
    @19
    wa
    @1
    c1
    cmin
    co
    cneg
    @16
    @2
    @1
    c1
    negsubdi
    @1
    c1
    negsubdi2
    eqtr3d
    sylancl
    fveq2d
    eqtr3d
    breqtrd
    @0
    @6
    @7
    c2
    @4
    clogb
    co
    #
    clt
    wbr
    #
    @8
    @0
    @6
    c2
    @5
    clogb
    co
    #
    @1
    clt
    wbr
    #
    @20
    cneg
    #
    @1
    clt
    wbr
    #
    @21
    @0
    @11
    @5
    crp
    wcel
    @0
    @6
    @23
    wb
    @11
    @0
    @13
    a1i
    #
    @0
    @4
    @0
    c2
    @3
    c2
    crp
    wcel
    @0
    2rp
    a1i
    @0
    @2
    @0
    c1
    @1
    @0
    1red
    @14
    resubcld
    flcld
    #
    rpexpcld
    #
    rpreccld
    @0
    id
    c2
    @5
    cR
    logblt
    syl3anc
    @0
    @22
    @24
    @1
    clt
    @0
    @11
    @4
    crp
    wcel
    #
    @22
    @24
    wceq
    @26
    @28
    @4
    c2
    logbrec
    syl2anc
    breq1d
    @0
    @20
    cr
    wcel
    #
    @12
    @25
    @21
    wb
    @0
    @11
    @29
    @30
    @26
    @28
    c2
    @4
    relogbzcl
    syl2anc
    @14
    @20
    @1
    ltnegcon1
    syl2anc
    3bitrd
    @0
    @20
    @3
    @7
    clt
    @0
    @11
    @3
    cz
    wcel
    @20
    @3
    wceq
    @26
    @27
    c2
    @3
    nnlogbexp
    syl2anc
    breq2d
    bitrd
    mpbird
end
