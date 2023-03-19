include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cdvds.mm"
include "cmin.mm"
include "co.mm"
include "wn.mm"
include "caddc.mm"
include "wi.mm"
include "cc0.mm"
include "cr.mm"
include "wb.mm"
include "nnre.mm"
include "posdif.mm"
include "syl2anr.mm"
include "pm5.32i.mm"
include "nnz.mm"
include "zsubcl.mm"
include "syl2an.mm"
include "elnnz.mm"
include "biimpri.mm"
include "sylan.mm"
include "sylbi.mm"
include "anasss.mm"
include "nngt0.mm"
include "ltsubpos.mm"
include "biimpd.mm"
include "expcom.mm"
include "mpdi.mm"
include "imp.mm"
include "adantrr.mm"
include "jca.mm"
include "3adant1.mm"
include "ndvdssub.mm"
include "syld3an3.mm"
include "zaddcl.mm"
include "sylan2.mm"
include "dvdssubr.mm"
include "an12s.mm"
include "3impb.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "nncn.mm"
include "subsub3.mm"
include "syl3an.mm"
include "breq2d.mm"
include "bitr4d.mm"
include "notbid.mm"
include "3adant3r.mm"
include "sylibrd.mm"

theorem ndvdsadd
  let cD: class D
  let cK: class K
  let cN: class N


  assert |- ( ( N e. ZZ /\ D e. NN /\ ( K e. NN /\ K < D ) ) -> ( D || N -> -. D || ( N + K ) ) )

  proof
    cN
    cz
    wcel
    #
    cD
    cn
    wcel
    #
    cK
    cn
    wcel
    #
    cK
    cD
    clt
    wbr
    #
    wa
    #
    w3a
    cD
    cN
    cdvds
    wbr
    #
    cD
    cN
    cD
    cK
    cmin
    co
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    wn
    #
    cD
    cN
    cK
    caddc
    co
    #
    cdvds
    wbr
    #
    wn
    #
    @0
    @1
    @4
    @6
    cn
    wcel
    #
    @6
    cD
    clt
    wbr
    #
    wa
    #
    @5
    @9
    wi
    @1
    @4
    @15
    @0
    @1
    @4
    wa
    @13
    @14
    @1
    @2
    @3
    @13
    @1
    @2
    wa
    #
    @3
    wa
    @16
    cc0
    @6
    clt
    wbr
    #
    wa
    @13
    @16
    @3
    @17
    @2
    cK
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    @3
    @17
    wb
    @1
    cK
    nnre
    #
    cD
    nnre
    #
    cK
    cD
    posdif
    syl2anr
    pm5.32i
    @16
    @6
    cz
    wcel
    #
    @17
    @13
    @1
    cD
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @22
    @2
    cD
    nnz
    #
    cK
    nnz
    #
    cD
    cK
    zsubcl
    syl2an
    @13
    @22
    @17
    wa
    @6
    elnnz
    biimpri
    sylan
    sylbi
    anasss
    @1
    @2
    @14
    @3
    @1
    @2
    @14
    @1
    @2
    cc0
    cK
    clt
    wbr
    #
    @14
    cK
    nngt0
    @2
    @1
    @27
    @14
    wi
    @2
    @1
    wa
    @27
    @14
    @2
    @18
    @19
    @27
    @14
    wb
    @1
    @20
    @21
    cK
    cD
    ltsubpos
    syl2an
    biimpd
    expcom
    mpdi
    imp
    adantrr
    jca
    3adant1
    cD
    @6
    cN
    ndvdssub
    syld3an3
    @0
    @1
    @2
    @12
    @9
    wb
    @3
    @0
    @1
    @2
    w3a
    #
    @11
    @8
    @28
    @11
    cD
    @10
    cD
    cmin
    co
    #
    cdvds
    wbr
    #
    @8
    @0
    @1
    @2
    @11
    @30
    wb
    #
    @1
    @0
    @2
    @31
    @1
    @23
    @10
    cz
    wcel
    #
    @31
    @0
    @2
    wa
    @25
    @2
    @0
    @24
    @32
    @26
    cN
    cK
    zaddcl
    sylan2
    cD
    @10
    dvdssubr
    syl2an
    an12s
    3impb
    @28
    @7
    @29
    cD
    cdvds
    @0
    cN
    cc
    wcel
    @1
    cD
    cc
    wcel
    @2
    cK
    cc
    wcel
    @7
    @29
    wceq
    cN
    zcn
    cD
    nncn
    cK
    nncn
    cN
    cD
    cK
    subsub3
    syl3an
    breq2d
    bitr4d
    notbid
    3adant3r
    sylibrd
end
