include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "eluz2.mm"
include "wa.mm"
include "simpr.mm"
include "adantr.mm"
include "zsubcl.mm"
include "adantlr.mm"
include "zsubcld.mm"
include "3jca.mm"
include "ex.mm"
include "3adant3.mm"
include "com12.mm"
include "imp.mm"
include "caddc.mm"
include "cc0.mm"
include "cr.mm"
include "zre.mm"
include "adantl.mm"
include "subge0d.mm"
include "exbiri.mm"
include "com23.mm"
include "3impia.mm"
include "impcom.mm"
include "resubcl.mm"
include "syl2anr.mm"
include "addge02d.mm"
include "mpbid.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "subsubd.mm"
include "breqtrrd.mm"
include "wb.mm"
include "subge0.mm"
include "imp31.mm"
include "subge02d.mm"
include "jca.mm"
include "elfz2.mm"
include "sylanbrc.mm"
include "3adant2.mm"
include "syl5bi.mm"
include "sylbi.mm"

theorem uzsubsubfz
  let cL: class L
  let cM: class M
  let cN: class N


  assert |- ( ( L e. ( ZZ>= ` M ) /\ N e. ( ZZ>= ` L ) ) -> ( N - ( L - M ) ) e. ( M ... N ) )

  proof
    cL
    cM
    cuz
    cfv
    wcel
    #
    cN
    cL
    cuz
    cfv
    wcel
    #
    cN
    cL
    cM
    cmin
    co
    #
    cmin
    co
    #
    cM
    cN
    cfz
    co
    wcel
    #
    @0
    cM
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    cM
    cL
    cle
    wbr
    #
    w3a
    #
    @1
    @4
    wi
    cM
    cL
    eluz2
    @1
    @6
    cN
    cz
    wcel
    #
    cL
    cN
    cle
    wbr
    #
    w3a
    #
    @8
    @4
    cL
    cN
    eluz2
    @5
    @7
    @11
    @4
    wi
    @6
    @5
    @7
    wa
    #
    @11
    @4
    @12
    @11
    wa
    #
    @5
    @9
    @3
    cz
    wcel
    #
    w3a
    #
    cM
    @3
    cle
    wbr
    #
    @3
    cN
    cle
    wbr
    #
    wa
    @4
    @12
    @11
    @15
    @5
    @11
    @15
    wi
    @7
    @11
    @5
    @15
    @6
    @9
    @5
    @15
    wi
    @10
    @6
    @9
    wa
    #
    @5
    @15
    @18
    @5
    wa
    #
    @5
    @9
    @14
    @18
    @5
    simpr
    @18
    @9
    @5
    @6
    @9
    simpr
    adantr
    #
    @19
    cN
    @2
    @20
    @6
    @5
    @2
    cz
    wcel
    @9
    cL
    cM
    zsubcl
    adantlr
    zsubcld
    3jca
    ex
    3adant3
    com12
    adantr
    imp
    @13
    @16
    @17
    @13
    cM
    cN
    cL
    cmin
    co
    #
    cM
    caddc
    co
    #
    @3
    cle
    @13
    cc0
    @21
    cle
    wbr
    #
    cM
    @22
    cle
    wbr
    @11
    @12
    @23
    @6
    @9
    @10
    @12
    @23
    wi
    @18
    @12
    @10
    @23
    @18
    @12
    @23
    @10
    @18
    @12
    wa
    cN
    cL
    @18
    cN
    cr
    wcel
    #
    @12
    @9
    @24
    @6
    cN
    zre
    #
    adantl
    adantr
    @18
    cL
    cr
    wcel
    #
    @12
    @6
    @26
    @9
    cL
    zre
    #
    adantr
    adantr
    subge0d
    exbiri
    com23
    3impia
    impcom
    @13
    cM
    @21
    @12
    cM
    cr
    wcel
    #
    @11
    @5
    @28
    @7
    cM
    zre
    #
    adantr
    #
    adantr
    @11
    @21
    cr
    wcel
    #
    @12
    @6
    @9
    @31
    @10
    @9
    @24
    @26
    @31
    @6
    @25
    @27
    cN
    cL
    resubcl
    syl2anr
    3adant3
    adantl
    addge02d
    mpbid
    @13
    cN
    cL
    cM
    @11
    cN
    cc
    wcel
    #
    @12
    @9
    @6
    @32
    @10
    cN
    zcn
    3ad2ant2
    adantl
    @11
    cL
    cc
    wcel
    #
    @12
    @6
    @9
    @33
    @10
    cL
    zcn
    3ad2ant1
    adantl
    @12
    cM
    cc
    wcel
    #
    @11
    @5
    @34
    @7
    cM
    zcn
    adantr
    adantr
    subsubd
    breqtrrd
    @13
    cc0
    @2
    cle
    wbr
    #
    @17
    @5
    @7
    @11
    @35
    @5
    @11
    @7
    @35
    @5
    @11
    @35
    @7
    @11
    @26
    @28
    @35
    @7
    wb
    @5
    @6
    @9
    @26
    @10
    @27
    3ad2ant1
    #
    @29
    cL
    cM
    subge0
    syl2anr
    exbiri
    com23
    imp31
    @13
    cN
    @2
    @11
    @24
    @12
    @9
    @6
    @24
    @10
    @25
    3ad2ant2
    adantl
    @11
    @26
    @28
    @2
    cr
    wcel
    @12
    @36
    @30
    cL
    cM
    resubcl
    syl2anr
    subge02d
    mpbid
    jca
    @3
    cM
    cN
    elfz2
    sylanbrc
    ex
    3adant2
    syl5bi
    sylbi
    imp
end
