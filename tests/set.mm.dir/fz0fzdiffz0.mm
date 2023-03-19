include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "fz0fzelfz0.mm"
include "elfzle1.mm"
include "adantl.mm"
include "wb.mm"
include "elfznn0.mm"
include "adantr.mm"
include "nn0sub.mm"
include "syl2anr.mm"
include "mpbid.mm"
include "elfz3nn0.mm"
include "wi.mm"
include "elfz2nn0.mm"
include "cz.mm"
include "elfz2.mm"
include "cr.mm"
include "zsubcl.mm"
include "zred.mm"
include "ancoms.mm"
include "3adant2.mm"
include "zre.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "nn0ge0.mm"
include "nn0re.mm"
include "subge02.mm"
include "syl2an.mm"
include "anim1i.mm"
include "letr.mm"
include "sylc.mm"
include "exp31.mm"
include "a1i.mm"
include "com14.mm"
include "impcom.mm"
include "sylbi.mm"
include "com13.mm"
include "3adant3.mm"
include "imp.mm"
include "mpancom.mm"
include "sylibr.mm"

theorem fz0fzdiffz0
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ( 0 ... N ) /\ K e. ( M ... N ) ) -> ( K - M ) e. ( 0 ... N ) )

  proof
    cM
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cK
    cM
    cN
    cfz
    co
    wcel
    #
    wa
    #
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
    @4
    cN
    cle
    wbr
    #
    w3a
    #
    @4
    @0
    wcel
    cK
    @0
    wcel
    #
    @3
    @8
    cN
    cK
    cM
    fz0fzelfz0
    @9
    @3
    wa
    #
    @5
    @6
    @7
    @10
    cM
    cK
    cle
    wbr
    #
    @5
    @3
    @11
    @9
    @2
    @11
    @1
    cK
    cM
    cN
    elfzle1
    adantl
    adantl
    @3
    cM
    cn0
    wcel
    #
    cK
    cn0
    wcel
    @11
    @5
    wb
    @9
    @1
    @12
    @2
    cM
    cN
    elfznn0
    adantr
    cK
    cN
    elfznn0
    cM
    cK
    nn0sub
    syl2anr
    mpbid
    @9
    @6
    @3
    cK
    cN
    elfz3nn0
    adantr
    @3
    @7
    @9
    @1
    @2
    @7
    @1
    @12
    @6
    cM
    cN
    cle
    wbr
    #
    w3a
    @2
    @7
    wi
    #
    cM
    cN
    elfz2nn0
    @12
    @6
    @14
    @13
    @6
    @12
    @14
    @2
    @12
    @6
    @7
    @2
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    @11
    cK
    cN
    cle
    wbr
    #
    wa
    #
    wa
    @12
    @6
    @7
    wi
    wi
    #
    cK
    cM
    cN
    elfz2
    @20
    @18
    @21
    @19
    @18
    @21
    wi
    @11
    @6
    @18
    @12
    @19
    @7
    @18
    @12
    @19
    @7
    wi
    wi
    wi
    @6
    @18
    @12
    @19
    @7
    @18
    @12
    wa
    #
    @19
    wa
    @4
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    @4
    cK
    cle
    wbr
    #
    @19
    wa
    @7
    @22
    @26
    @19
    @18
    @26
    @12
    @18
    @23
    @24
    @25
    @15
    @17
    @23
    @16
    @17
    @15
    @23
    @17
    @15
    wa
    @4
    cK
    cM
    zsubcl
    zred
    ancoms
    3adant2
    @17
    @15
    @24
    @16
    cK
    zre
    3ad2ant3
    #
    @16
    @15
    @25
    @17
    cN
    zre
    3ad2ant2
    3jca
    adantr
    adantr
    @22
    @27
    @19
    @22
    cc0
    cM
    cle
    wbr
    #
    @27
    @12
    @29
    @18
    cM
    nn0ge0
    adantl
    @18
    @24
    cM
    cr
    wcel
    @29
    @27
    wb
    @12
    @28
    cM
    nn0re
    cK
    cM
    subge02
    syl2an
    mpbid
    anim1i
    @4
    cK
    cN
    letr
    sylc
    exp31
    a1i
    com14
    adantl
    impcom
    sylbi
    com13
    impcom
    3adant3
    sylbi
    imp
    adantl
    3jca
    mpancom
    @4
    cN
    elfz2nn0
    sylibr
end
