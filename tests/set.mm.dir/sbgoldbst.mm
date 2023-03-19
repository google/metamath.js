include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "c7.mm"
include "cgbo.mm"
include "codd.mm"
include "wa.mm"
include "c3.mm"
include "cmin.mm"
include "co.mm"
include "simpl.mm"
include "3odd.mm"
include "jctir.mm"
include "omoeALTV.mm"
include "wceq.mm"
include "breq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "3syl.mm"
include "caddc.mm"
include "4p3e7.mm"
include "breq1i.mm"
include "cr.mm"
include "4re.mm"
include "a1i.mm"
include "3re.mm"
include "oddz.mm"
include "zred.mm"
include "ltaddsubd.mm"
include "biimpd.mm"
include "syl5bir.mm"
include "imp.mm"
include "pm2.27.mm"
include "syl.mm"
include "w3a.mm"
include "cprime.mm"
include "wrex.mm"
include "isgbe.mm"
include "3prm.mm"
include "wb.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "simp1.mm"
include "simp2.mm"
include "3jca.mm"
include "cc.mm"
include "zcnd.mm"
include "ad3antrrr.mm"
include "3cn.mm"
include "cz.mm"
include "prmz.mm"
include "zaddcl.mm"
include "syl2an.mm"
include "adantll.mm"
include "subadd2d.mm"
include "biimpa.mm"
include "eqcomd.mm"
include "3ad2antr3.mm"
include "jca.mm"
include "rspcedvd.mm"
include "ex.mm"
include "reximdva.mm"
include "jctild.mm"
include "isgbo.mm"
include "syl6ibr.mm"
include "adantld.mm"
include "syl5bi.mm"
include "3syld.mm"
include "com12.mm"
include "expd.mm"
include "ralrimiv.mm"

theorem sbgoldbst
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x

  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) -> A. m e. Odd ( 7 < m -> m e. GoldbachOdd ) )

  proof
    c4
    vn
    cv
    #
    clt
    wbr
    #
    @0
    cgbe
    wcel
    #
    wi
    #
    vn
    ceven
    wral
    #
    c7
    vm
    cv
    #
    clt
    wbr
    #
    @5
    cgbo
    wcel
    #
    wi
    vm
    codd
    @4
    @5
    codd
    wcel
    #
    @6
    @7
    @8
    @6
    wa
    #
    @4
    @7
    @9
    @4
    c4
    @5
    c3
    cmin
    co
    #
    clt
    wbr
    #
    @10
    cgbe
    wcel
    #
    wi
    #
    @12
    @7
    @9
    @8
    c3
    codd
    wcel
    #
    wa
    @10
    ceven
    wcel
    #
    @4
    @13
    wi
    @9
    @8
    @14
    @8
    @6
    simpl
    #
    3odd
    jctir
    @5
    c3
    omoeALTV
    @3
    @13
    vn
    @10
    ceven
    @0
    @10
    wceq
    @1
    @11
    @2
    @12
    @0
    @10
    c4
    clt
    breq2
    @0
    @10
    cgbe
    eleq1
    imbi12d
    rspcv
    3syl
    @9
    @11
    @13
    @12
    wi
    @8
    @6
    @11
    @6
    c4
    c3
    caddc
    co
    #
    @5
    clt
    wbr
    #
    @8
    @11
    @17
    c7
    @5
    clt
    4p3e7
    breq1i
    @8
    @18
    @11
    @8
    c4
    c3
    @5
    c4
    cr
    wcel
    @8
    4re
    a1i
    c3
    cr
    wcel
    @8
    3re
    a1i
    @8
    @5
    @5
    oddz
    #
    zred
    ltaddsubd
    biimpd
    syl5bir
    imp
    @11
    @12
    pm2.27
    syl
    @12
    @15
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    @10
    @20
    @22
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    @9
    @7
    @10
    vq
    vp
    isgbe
    @9
    @28
    @7
    @15
    @9
    @28
    @8
    @21
    @23
    vr
    cv
    #
    codd
    wcel
    #
    w3a
    #
    @5
    @24
    @29
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    @7
    @9
    @28
    @37
    @8
    @9
    @27
    @36
    vp
    cprime
    @9
    @20
    cprime
    wcel
    #
    wa
    #
    @26
    @35
    vq
    cprime
    @39
    @22
    cprime
    wcel
    #
    wa
    #
    @26
    @35
    @41
    @26
    wa
    #
    @34
    @21
    @23
    @14
    w3a
    #
    @5
    @24
    c3
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    c3
    cprime
    c3
    cprime
    wcel
    @42
    3prm
    a1i
    @29
    c3
    wceq
    #
    @34
    @46
    wb
    @42
    @47
    @31
    @43
    @33
    @45
    @47
    @30
    @14
    @21
    @23
    @29
    c3
    codd
    eleq1
    3anbi3d
    @47
    @32
    @44
    @5
    @29
    c3
    @24
    caddc
    oveq2
    eqeq2d
    anbi12d
    adantl
    @42
    @43
    @45
    @26
    @43
    @41
    @26
    @21
    @23
    @14
    @21
    @23
    @25
    simp1
    @21
    @23
    @25
    simp2
    @14
    @26
    3odd
    a1i
    3jca
    adantl
    @41
    @21
    @25
    @45
    @23
    @41
    @25
    wa
    @44
    @5
    @41
    @25
    @44
    @5
    wceq
    @41
    @5
    c3
    @24
    @8
    @5
    cc
    wcel
    @6
    @38
    @40
    @8
    @5
    @19
    zcnd
    ad3antrrr
    c3
    cc
    wcel
    @41
    3cn
    a1i
    @38
    @40
    @24
    cc
    wcel
    @9
    @38
    @40
    wa
    @24
    @38
    @20
    cz
    wcel
    @22
    cz
    wcel
    @24
    cz
    wcel
    @40
    @20
    prmz
    @22
    prmz
    @20
    @22
    zaddcl
    syl2an
    zcnd
    adantll
    subadd2d
    biimpa
    eqcomd
    3ad2antr3
    jca
    rspcedvd
    ex
    reximdva
    reximdva
    @16
    jctild
    @5
    vr
    vq
    vp
    isgbo
    syl6ibr
    adantld
    syl5bi
    3syld
    com12
    expd
    ralrimiv
end
