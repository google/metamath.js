include "wne.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cfzo.mm"
include "cle.mm"
include "wi.mm"
include "elfz2nn0.mm"
include "simpl1.mm"
include "necom.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "ltlen.mm"
include "syl2an.mm"
include "bicomd.mm"
include "cz.mm"
include "elnn0z.mm"
include "0red.mm"
include "zre.mm"
include "adantr.mm"
include "adantl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "nn0z.mm"
include "elnnz.mm"
include "simplbi2.mm"
include "syl.mm"
include "syld.mm"
include "expd.mm"
include "impancom.mm"
include "sylbi.mm"
include "imp.mm"
include "sylbid.mm"
include "syl7bi.mm"
include "3impia.mm"
include "biimpd.mm"
include "exp4b.mm"
include "3imp.mm"
include "syl5bi.mm"
include "3jca.mm"
include "ex.mm"
include "impcom.mm"
include "elfzo0.mm"
include "sylibr.mm"

theorem fzofzim
  let cK: class K
  let cM: class M


  assert |- ( ( K =/= M /\ K e. ( 0 ... M ) ) -> K e. ( 0 ..^ M ) )

  proof
    cK
    cM
    wne
    #
    cK
    cc0
    cM
    cfz
    co
    wcel
    #
    wa
    cK
    cn0
    wcel
    #
    cM
    cn
    wcel
    #
    cK
    cM
    clt
    wbr
    #
    w3a
    #
    cK
    cc0
    cM
    cfzo
    co
    wcel
    @1
    @0
    @5
    @1
    @2
    cM
    cn0
    wcel
    #
    cK
    cM
    cle
    wbr
    #
    w3a
    #
    @0
    @5
    wi
    cK
    cM
    elfz2nn0
    @8
    @0
    @5
    @8
    @0
    wa
    @2
    @3
    @4
    @2
    @6
    @7
    @0
    simpl1
    @8
    @0
    @3
    @2
    @6
    @7
    @0
    @3
    wi
    @0
    cM
    cK
    wne
    #
    @2
    @6
    wa
    #
    @7
    @3
    cK
    cM
    necom
    #
    @10
    @7
    @9
    @3
    @10
    @7
    @9
    wa
    #
    @4
    @3
    @10
    @4
    @12
    @2
    cK
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @4
    @12
    wb
    @6
    cK
    nn0re
    cM
    nn0re
    #
    cK
    cM
    ltlen
    syl2an
    bicomd
    #
    @2
    @6
    @4
    @3
    wi
    #
    @2
    cK
    cz
    wcel
    #
    cc0
    cK
    cle
    wbr
    #
    wa
    @6
    @17
    wi
    cK
    elnn0z
    @18
    @6
    @19
    @17
    @18
    @6
    wa
    #
    @19
    @4
    @3
    @20
    @19
    @4
    wa
    #
    cc0
    cM
    clt
    wbr
    #
    @3
    @20
    cc0
    cr
    wcel
    @13
    @14
    @21
    @22
    wi
    @20
    0red
    @18
    @13
    @6
    cK
    zre
    adantr
    @6
    @14
    @18
    @15
    adantl
    cc0
    cK
    cM
    lelttr
    syl3anc
    @6
    @22
    @3
    wi
    #
    @18
    @6
    cM
    cz
    wcel
    #
    @23
    cM
    nn0z
    @3
    @24
    @22
    cM
    elnnz
    simplbi2
    syl
    adantl
    syld
    expd
    impancom
    sylbi
    imp
    sylbid
    expd
    syl7bi
    3impia
    imp
    @8
    @0
    @4
    @0
    @9
    @8
    @4
    @11
    @2
    @6
    @7
    @9
    @4
    wi
    @2
    @6
    @7
    @9
    @4
    @10
    @12
    @4
    @16
    biimpd
    exp4b
    3imp
    syl5bi
    imp
    3jca
    ex
    sylbi
    impcom
    cK
    cM
    elfzo0
    sylibr
end
