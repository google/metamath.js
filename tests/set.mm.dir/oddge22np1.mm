include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cn.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "eleq1.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "nn0z.mm"
include "adantl.mm"
include "cle.mm"
include "w3a.mm"
include "eluz2.mm"
include "cmin.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "1red.mm"
include "2nn0.mm"
include "id.mm"
include "nn0mulcld.mm"
include "nn0red.mm"
include "lesubaddd.mm"
include "2m1e1.mm"
include "breq1i.mm"
include "cdiv.mm"
include "wb.mm"
include "nn0re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ledivmul.mm"
include "syl3anc.mm"
include "halfgt0.mm"
include "0red.mm"
include "halfre.mm"
include "ltletr.mm"
include "mpani.mm"
include "sylbird.mm"
include "syl5bi.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "imp.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "ex.mm"
include "syl6bir.mm"
include "com13.mm"
include "impcom.mm"
include "pm4.71rd.mm"
include "bicomd.mm"
include "rexbidva.mm"
include "wss.mm"
include "nnssnn0.mm"
include "rexss.mm"
include "mp1i.mm"
include "eluzge2nn0.mm"
include "oddnn02np1.mm"
include "syl.mm"
include "3bitr4rd.mm"

theorem oddge22np1
  let vn: setvar n
  let cN: class N

  disjoint N n
  assert |- ( N e. ( ZZ>= ` 2 ) -> ( -. 2 || N <-> E. n e. NN ( ( 2 x. n ) + 1 ) = N ) )

  proof
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    vn
    cv
    #
    cn
    wcel
    #
    c2
    @2
    cmul
    co
    #
    c1
    caddc
    co
    #
    cN
    wceq
    #
    wa
    #
    vn
    cn0
    wrex
    #
    @6
    vn
    cn0
    wrex
    #
    @6
    vn
    cn
    wrex
    #
    c2
    cN
    cdvds
    wbr
    wn
    #
    @1
    @7
    @6
    vn
    cn0
    @1
    @2
    cn0
    wcel
    #
    wa
    #
    @6
    @7
    @13
    @6
    @3
    @12
    @1
    @6
    @3
    wi
    @6
    @1
    @12
    @3
    @6
    @1
    @5
    @0
    wcel
    #
    @12
    @3
    wi
    @5
    cN
    @0
    eleq1
    @14
    @12
    @3
    @14
    @12
    wa
    @2
    cz
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @3
    @12
    @15
    @14
    @2
    nn0z
    adantl
    @14
    @12
    @16
    @14
    c2
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    c2
    @5
    cle
    wbr
    #
    w3a
    @12
    @16
    wi
    #
    c2
    @5
    eluz2
    @19
    @17
    @20
    @18
    @12
    @19
    @16
    @12
    @19
    c2
    c1
    cmin
    co
    #
    @4
    cle
    wbr
    #
    @16
    @12
    c2
    c1
    @4
    c2
    cr
    wcel
    #
    @12
    2re
    a1i
    @12
    1red
    #
    @12
    @4
    @12
    c2
    @2
    c2
    cn0
    wcel
    @12
    2nn0
    a1i
    @12
    id
    nn0mulcld
    nn0red
    lesubaddd
    @22
    c1
    @4
    cle
    wbr
    #
    @12
    @16
    @21
    c1
    @4
    cle
    2m1e1
    breq1i
    @12
    @25
    c1
    c2
    cdiv
    co
    #
    @2
    cle
    wbr
    #
    @16
    @12
    c1
    cr
    wcel
    @2
    cr
    wcel
    #
    @23
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @27
    @25
    wb
    @24
    @2
    nn0re
    #
    @30
    @12
    @23
    @29
    2re
    2pos
    pm3.2i
    a1i
    c1
    @2
    c2
    ledivmul
    syl3anc
    @12
    cc0
    @26
    clt
    wbr
    #
    @27
    @16
    halfgt0
    @12
    cc0
    cr
    wcel
    @26
    cr
    wcel
    #
    @28
    @32
    @27
    wa
    @16
    wi
    @12
    0red
    @33
    @12
    halfre
    a1i
    @31
    cc0
    @26
    @2
    ltletr
    syl3anc
    mpani
    sylbird
    syl5bi
    sylbird
    com12
    3ad2ant3
    sylbi
    imp
    @2
    elnnz
    sylanbrc
    ex
    syl6bir
    com13
    impcom
    pm4.71rd
    bicomd
    rexbidva
    cn
    cn0
    wss
    @10
    @8
    wb
    @1
    nnssnn0
    @6
    vn
    cn
    cn0
    rexss
    mp1i
    @1
    cN
    cn0
    wcel
    @11
    @9
    wb
    cN
    eluzge2nn0
    vn
    cN
    oddnn02np1
    syl
    3bitr4rd
end
