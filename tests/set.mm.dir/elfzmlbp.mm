include "cz.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cmin.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "elfz2.mm"
include "wi.mm"
include "wb.mm"
include "znn0sub.mm"
include "adantr.mm"
include "biimpcd.mm"
include "impcom.mm"
include "cr.mm"
include "zre.mm"
include "adantl.mm"
include "zaddcl.mm"
include "adantlr.mm"
include "zred.mm"
include "letr.mm"
include "syl3anc.mm"
include "addge01.mm"
include "syl2an.mm"
include "elnn0z.mm"
include "simplbi2.mm"
include "sylbird.mm"
include "syld.mm"
include "imp.mm"
include "df-3an.mm"
include "3ancoma.mm"
include "bitr3i.mm"
include "3anim123i.mm"
include "sylbi.mm"
include "lesubadd2.mm"
include "syl.mm"
include "biimprcd.mm"
include "3jca.mm"
include "exp31.mm"
include "com23.mm"
include "3adant2.mm"
include "com12.mm"
include "syl5bi.mm"
include "elfz2nn0.mm"
include "sylibr.mm"

theorem elfzmlbp
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ K e. ( M ... ( M + N ) ) ) -> ( K - M ) e. ( 0 ... N ) )

  proof
    cN
    cz
    wcel
    #
    cK
    cM
    cM
    cN
    caddc
    co
    #
    cfz
    co
    wcel
    #
    wa
    cK
    cM
    cmin
    co
    #
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    @3
    cN
    cle
    wbr
    #
    w3a
    #
    @3
    cc0
    cN
    cfz
    co
    wcel
    @0
    @2
    @7
    @2
    cM
    cz
    wcel
    #
    @1
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    cM
    cK
    cle
    wbr
    #
    cK
    @1
    cle
    wbr
    #
    wa
    #
    wa
    #
    @0
    @7
    cK
    cM
    @1
    elfz2
    @15
    @0
    @7
    @11
    @14
    @0
    @7
    wi
    #
    @8
    @10
    @14
    @16
    wi
    @9
    @8
    @10
    wa
    #
    @0
    @14
    @7
    @17
    @0
    @14
    @7
    @17
    @0
    wa
    #
    @14
    wa
    @4
    @5
    @6
    @14
    @18
    @4
    @12
    @18
    @4
    wi
    @13
    @18
    @12
    @4
    @17
    @12
    @4
    wb
    @0
    cM
    cK
    znn0sub
    adantr
    biimpcd
    adantr
    impcom
    @18
    @14
    @5
    @18
    @14
    cM
    @1
    cle
    wbr
    #
    @5
    @18
    cM
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    @1
    cr
    wcel
    @14
    @19
    wi
    @17
    @20
    @0
    @8
    @20
    @10
    cM
    zre
    #
    adantr
    #
    adantr
    @17
    @21
    @0
    @10
    @21
    @8
    cK
    zre
    #
    adantl
    adantr
    @18
    @1
    @8
    @0
    @9
    @10
    cM
    cN
    zaddcl
    adantlr
    zred
    cM
    cK
    @1
    letr
    syl3anc
    @18
    @19
    cc0
    cN
    cle
    wbr
    #
    @5
    @17
    @20
    cN
    cr
    wcel
    #
    @25
    @19
    wb
    @0
    @23
    cN
    zre
    #
    cM
    cN
    addge01
    syl2an
    @0
    @25
    @5
    wi
    @17
    @5
    @0
    @25
    cN
    elnn0z
    simplbi2
    adantl
    sylbird
    syld
    imp
    @14
    @18
    @6
    @13
    @18
    @6
    wi
    @12
    @18
    @6
    @13
    @18
    @21
    @20
    @26
    w3a
    #
    @6
    @13
    wb
    @18
    @10
    @8
    @0
    w3a
    #
    @28
    @18
    @8
    @10
    @0
    w3a
    @29
    @8
    @10
    @0
    df-3an
    @8
    @10
    @0
    3ancoma
    bitr3i
    @10
    @21
    @8
    @20
    @0
    @26
    @24
    @22
    @27
    3anim123i
    sylbi
    cK
    cM
    cN
    lesubadd2
    syl
    biimprcd
    adantl
    impcom
    3jca
    exp31
    com23
    3adant2
    imp
    com12
    syl5bi
    imp
    @3
    cN
    elfz2nn0
    sylibr
end
