include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "cn0.mm"
include "cz.mm"
include "wa.mm"
include "wi.mm"
include "elfznn0.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "adantr.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "subge0.mm"
include "biimpar.mm"
include "jca.mm"
include "exp31.mm"
include "syl2im.mm"
include "3imp.mm"
include "elnn0z.mm"
include "sylibr.mm"
include "elfz3nn0.mm"
include "3ad2ant1.mm"
include "elfz2nn0.mm"
include "resubcl.mm"
include "syl2an.mm"
include "3ad2ant2.mm"
include "nn0ge0.mm"
include "adantl.mm"
include "subge02.mm"
include "mpbid.mm"
include "simpl3.mm"
include "letrd.mm"
include "ex.mm"
include "sylbi.mm"
include "syl5com.mm"
include "a1dd.mm"
include "syl3anbrc.mm"

theorem difelfzle
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ( 0 ... N ) /\ M e. ( 0 ... N ) /\ K <_ M ) -> ( M - K ) e. ( 0 ... N ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cM
    @0
    wcel
    #
    cK
    cM
    cle
    wbr
    #
    w3a
    #
    cM
    cK
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
    @5
    cN
    cle
    wbr
    #
    @5
    @0
    wcel
    @4
    @5
    cz
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    wa
    #
    @6
    @1
    @2
    @3
    @11
    @1
    cK
    cn0
    wcel
    #
    @2
    cM
    cn0
    wcel
    #
    @3
    @11
    wi
    cK
    cN
    elfznn0
    #
    cM
    cN
    elfznn0
    @12
    @13
    @3
    @11
    @12
    @13
    wa
    #
    @3
    wa
    @9
    @10
    @15
    @9
    @3
    @13
    cM
    cz
    wcel
    cK
    cz
    wcel
    @9
    @12
    cM
    nn0z
    cK
    nn0z
    cM
    cK
    zsubcl
    syl2anr
    adantr
    @15
    @10
    @3
    @13
    cM
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    @10
    @3
    wb
    @12
    cM
    nn0re
    #
    cK
    nn0re
    #
    cM
    cK
    subge0
    syl2anr
    biimpar
    jca
    exp31
    syl2im
    3imp
    @5
    elnn0z
    sylibr
    @1
    @2
    @7
    @3
    cK
    cN
    elfz3nn0
    3ad2ant1
    @1
    @2
    @3
    @8
    @1
    @2
    @8
    @3
    @1
    @12
    @2
    @8
    @14
    @2
    @13
    @7
    cM
    cN
    cle
    wbr
    #
    w3a
    #
    @12
    @8
    wi
    cM
    cN
    elfz2nn0
    @21
    @12
    @8
    @21
    @12
    wa
    #
    @5
    cM
    cN
    @21
    @16
    @17
    @5
    cr
    wcel
    @12
    @13
    @7
    @16
    @20
    @18
    3ad2ant1
    #
    @19
    cM
    cK
    resubcl
    syl2an
    @21
    @16
    @12
    @23
    adantr
    @21
    cN
    cr
    wcel
    #
    @12
    @7
    @13
    @24
    @20
    cN
    nn0re
    3ad2ant2
    adantr
    @22
    cc0
    cK
    cle
    wbr
    #
    @5
    cM
    cle
    wbr
    #
    @12
    @25
    @21
    cK
    nn0ge0
    adantl
    @21
    @16
    @17
    @25
    @26
    wb
    @12
    @23
    @19
    cM
    cK
    subge02
    syl2an
    mpbid
    @13
    @7
    @20
    @12
    simpl3
    letrd
    ex
    sylbi
    syl5com
    a1dd
    3imp
    @5
    cN
    elfz2nn0
    syl3anbrc
end
