include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cicc.mm"
include "wcel.mm"
include "cioo.mm"
include "cpr.mm"
include "wo.mm"
include "csin.mm"
include "cfv.mm"
include "casin.mm"
include "wceq.mm"
include "cun.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "neghalfpire.mm"
include "rexri.mm"
include "halfpire.mm"
include "cc0.mm"
include "clt.mm"
include "crp.mm"
include "pirp.mm"
include "rphalfcl.mm"
include "ax-mp.mm"
include "rpgt0.mm"
include "cr.mm"
include "wb.mm"
include "lt0neg2.mm"
include "mpbi.mm"
include "0re.mm"
include "lttri.mm"
include "mp2an.mm"
include "ltleii.mm"
include "prunioo.mm"
include "mp3an.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitr3i.mm"
include "cc.mm"
include "cre.mm"
include "elioore.mm"
include "recnd.mm"
include "rered.mm"
include "id.mm"
include "eqeltrd.mm"
include "asinsin.mm"
include "syl2anc.mm"
include "elpri.mm"
include "c1.mm"
include "ax-1cn.mm"
include "asinneg.mm"
include "asin1.mm"
include "negeqi.mm"
include "eqtri.mm"
include "fveq2.mm"
include "recni.mm"
include "sinneg.mm"
include "sinhalfpi.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "jaoi.mm"
include "syl.mm"
include "sylbi.mm"

theorem reasinsin
  let cA: class A


  assert |- ( A e. ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) -> ( arcsin ` ( sin ` A ) ) = A )

  proof
    cA
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @0
    cicc
    co
    #
    wcel
    #
    cA
    @1
    @0
    cioo
    co
    #
    wcel
    #
    cA
    @1
    @0
    cpr
    #
    wcel
    #
    wo
    #
    cA
    csin
    cfv
    #
    casin
    cfv
    #
    cA
    wceq
    #
    @3
    cA
    @4
    @6
    cun
    #
    wcel
    @8
    @12
    @2
    cA
    @1
    cxr
    wcel
    @0
    cxr
    wcel
    @1
    @0
    cle
    wbr
    @12
    @2
    wceq
    @1
    neghalfpire
    rexri
    @0
    halfpire
    rexri
    @1
    @0
    neghalfpire
    halfpire
    @1
    cc0
    clt
    wbr
    #
    cc0
    @0
    clt
    wbr
    #
    @1
    @0
    clt
    wbr
    @14
    @13
    @0
    crp
    wcel
    #
    @14
    cpi
    crp
    wcel
    @15
    pirp
    cpi
    rphalfcl
    ax-mp
    @0
    rpgt0
    ax-mp
    #
    @0
    cr
    wcel
    @14
    @13
    wb
    halfpire
    @0
    lt0neg2
    ax-mp
    mpbi
    @16
    @1
    cc0
    @0
    neghalfpire
    0re
    halfpire
    lttri
    mp2an
    ltleii
    @1
    @0
    prunioo
    mp3an
    eleq2i
    cA
    @4
    @6
    elun
    bitr3i
    @5
    @11
    @7
    @5
    cA
    cc
    wcel
    cA
    cre
    cfv
    #
    @4
    wcel
    @11
    @5
    cA
    cA
    @1
    @0
    elioore
    #
    recnd
    @5
    @17
    cA
    @4
    @5
    cA
    @18
    rered
    @5
    id
    eqeltrd
    cA
    asinsin
    syl2anc
    @7
    cA
    @1
    wceq
    #
    cA
    @0
    wceq
    #
    wo
    @11
    cA
    @1
    @0
    elpri
    @19
    @11
    @20
    @19
    c1
    cneg
    #
    casin
    cfv
    #
    @1
    @10
    cA
    @22
    c1
    casin
    cfv
    #
    cneg
    #
    @1
    c1
    cc
    wcel
    @22
    @24
    wceq
    ax-1cn
    c1
    asinneg
    ax-mp
    @23
    @0
    asin1
    negeqi
    eqtri
    @19
    @9
    @21
    casin
    @19
    @9
    @1
    csin
    cfv
    #
    @21
    cA
    @1
    csin
    fveq2
    @25
    @0
    csin
    cfv
    #
    cneg
    #
    @21
    @0
    cc
    wcel
    @25
    @27
    wceq
    @0
    halfpire
    recni
    @0
    sinneg
    ax-mp
    @26
    c1
    sinhalfpi
    negeqi
    eqtri
    syl6eq
    fveq2d
    @19
    id
    3eqtr4a
    @20
    @23
    @0
    @10
    cA
    asin1
    @20
    @9
    c1
    casin
    @20
    @9
    @26
    c1
    cA
    @0
    csin
    fveq2
    sinhalfpi
    syl6eq
    fveq2d
    @20
    id
    3eqtr4a
    jaoi
    syl
    jaoi
    sylbi
end
