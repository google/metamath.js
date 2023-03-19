include "c1.mm"
include "casin.mm"
include "cfv.mm"
include "ci.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "caddc.mm"
include "clog.mm"
include "cpi.mm"
include "cdiv.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "asinval.mm"
include "ax-mp.mm"
include "ce.mm"
include "cc0.mm"
include "ax-icn.mm"
include "addid1i.mm"
include "mulid1i.mm"
include "sq1.mm"
include "oveq2i.mm"
include "1m1e0.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "sqrt0.mm"
include "oveq12i.mm"
include "efhalfpi.mm"
include "3eqtr4i.mm"
include "crn.mm"
include "cim.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "halfpire.mm"
include "recni.mm"
include "mulcli.mm"
include "pipos.mm"
include "cr.mm"
include "wb.mm"
include "pire.mm"
include "lt0neg2.mm"
include "mpbi.mm"
include "crp.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "rpgt0.mm"
include "renegcli.mm"
include "0re.mm"
include "lttri.mm"
include "mp2an.mm"
include "addid2i.mm"
include "crimi.mm"
include "eqtr3i.mm"
include "breqtrri.mm"
include "rphalflt.mm"
include "ltleii.mm"
include "eqbrtri.mm"
include "ellogrn.mm"
include "mpbir3an.mm"
include "logef.mm"
include "mulneg1i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "negicn.mm"
include "mulassi.mm"
include "mulid2i.mm"

theorem asin1



  assert |- ( arcsin ` 1 ) = ( _pi / 2 )

  proof
    c1
    casin
    cfv
    #
    ci
    cneg
    #
    ci
    c1
    cmul
    co
    #
    c1
    c1
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
    clog
    cfv
    #
    cmul
    co
    #
    @1
    ci
    cpi
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    @9
    c1
    cc
    wcel
    @0
    @8
    wceq
    ax-1cn
    c1
    asinval
    ax-mp
    @7
    @10
    @1
    cmul
    @7
    @10
    ce
    cfv
    #
    clog
    cfv
    #
    @10
    @6
    @12
    clog
    ci
    cc0
    caddc
    co
    ci
    @6
    @12
    ci
    ax-icn
    addid1i
    @2
    ci
    @5
    cc0
    caddc
    ci
    ax-icn
    mulid1i
    @5
    cc0
    csqrt
    cfv
    cc0
    @4
    cc0
    csqrt
    @4
    c1
    c1
    cmin
    co
    cc0
    @3
    c1
    c1
    cmin
    sq1
    oveq2i
    1m1e0
    eqtri
    fveq2i
    sqrt0
    eqtri
    oveq12i
    efhalfpi
    3eqtr4i
    fveq2i
    @10
    clog
    crn
    wcel
    #
    @13
    @10
    wceq
    @14
    @10
    cc
    wcel
    cpi
    cneg
    #
    @10
    cim
    cfv
    #
    clt
    wbr
    @16
    cpi
    cle
    wbr
    ci
    @9
    ax-icn
    @9
    halfpire
    recni
    #
    mulcli
    #
    @15
    @9
    @16
    clt
    @15
    cc0
    clt
    wbr
    #
    cc0
    @9
    clt
    wbr
    #
    @15
    @9
    clt
    wbr
    cc0
    cpi
    clt
    wbr
    #
    @19
    pipos
    cpi
    cr
    wcel
    @21
    @19
    wb
    pire
    cpi
    lt0neg2
    ax-mp
    mpbi
    @9
    crp
    wcel
    #
    @20
    cpi
    crp
    wcel
    #
    @22
    pirp
    cpi
    rphalfcl
    ax-mp
    @9
    rpgt0
    ax-mp
    @15
    cc0
    @9
    cpi
    pire
    renegcli
    0re
    halfpire
    lttri
    mp2an
    cc0
    @10
    caddc
    co
    #
    cim
    cfv
    @16
    @9
    @24
    @10
    cim
    @10
    @18
    addid2i
    fveq2i
    cc0
    @9
    0re
    halfpire
    crimi
    eqtr3i
    #
    breqtrri
    @16
    @9
    cpi
    cle
    @25
    @9
    cpi
    halfpire
    pire
    @23
    @9
    cpi
    clt
    wbr
    pirp
    cpi
    rphalflt
    ax-mp
    ltleii
    eqbrtri
    @10
    ellogrn
    mpbir3an
    @10
    logef
    ax-mp
    eqtri
    oveq2i
    c1
    @9
    cmul
    co
    #
    @11
    @9
    @1
    ci
    cmul
    co
    #
    @9
    cmul
    co
    @26
    @11
    @27
    c1
    @9
    cmul
    @27
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
    mulneg1i
    @28
    @29
    ixi
    negeqi
    negneg1e1
    3eqtri
    oveq1i
    @1
    ci
    @9
    negicn
    ax-icn
    @17
    mulassi
    eqtr3i
    @9
    @17
    mulid2i
    eqtr3i
    3eqtri
end
