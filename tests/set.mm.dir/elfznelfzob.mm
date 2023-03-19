include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "elfznelfzo.mm"
include "ex.mm"
include "wi.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "elfzole1.mm"
include "clt.mm"
include "cz.mm"
include "elfzolt2.mm"
include "elfzoel2.mm"
include "elfzoelz.mm"
include "0lt1.mm"
include "breq1.mm"
include "mpbiri.mm"
include "cr.mm"
include "zre.mm"
include "adantl.mm"
include "1red.mm"
include "ltnled.mm"
include "syl5ib.mm"
include "con2d.mm"
include "wne.mm"
include "wb.mm"
include "ltlen.mm"
include "syl2anr.mm"
include "necom.mm"
include "df-ne.mm"
include "sylbb.mm"
include "syl6bi.mm"
include "com23.mm"
include "impcom.mm"
include "imp.mm"
include "jctird.mm"
include "syl21anc.mm"
include "mpd.mm"
include "ioran.mm"
include "sylibr.mm"
include "a1i.mm"
include "impbid.mm"

theorem elfznelfzob
  let cK: class K
  let cM: class M


  assert |- ( M e. ( 0 ... K ) -> ( -. M e. ( 1 ..^ K ) <-> ( M = 0 \/ M = K ) ) )

  proof
    cM
    cc0
    cK
    cfz
    co
    wcel
    #
    cM
    c1
    cK
    cfzo
    co
    wcel
    #
    wn
    #
    cM
    cc0
    wceq
    #
    cM
    cK
    wceq
    #
    wo
    #
    @0
    @2
    @5
    cK
    cM
    elfznelfzo
    ex
    @0
    @1
    @5
    @1
    @5
    wn
    #
    wi
    @0
    @1
    @3
    wn
    #
    @4
    wn
    #
    wa
    #
    @6
    @1
    c1
    cM
    cle
    wbr
    #
    @9
    cM
    c1
    cK
    elfzole1
    @1
    cM
    cK
    clt
    wbr
    #
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @10
    @9
    wi
    cM
    c1
    cK
    elfzolt2
    cM
    c1
    cK
    elfzoel2
    cM
    c1
    cK
    elfzoelz
    @11
    @12
    wa
    #
    @13
    wa
    #
    @10
    @7
    @8
    @15
    @3
    @10
    @3
    cM
    c1
    clt
    wbr
    #
    @15
    @10
    wn
    @3
    @16
    cc0
    c1
    clt
    wbr
    0lt1
    cM
    cc0
    c1
    clt
    breq1
    mpbiri
    @15
    cM
    c1
    @13
    cM
    cr
    wcel
    #
    @14
    cM
    zre
    #
    adantl
    @15
    1red
    ltnled
    syl5ib
    con2d
    @14
    @13
    @8
    @12
    @11
    @13
    @8
    wi
    @12
    @13
    @11
    @8
    @12
    @13
    @11
    @8
    wi
    @12
    @13
    wa
    @11
    cM
    cK
    cle
    wbr
    #
    cK
    cM
    wne
    #
    wa
    #
    @8
    @13
    @17
    cK
    cr
    wcel
    @11
    @21
    wb
    @12
    @18
    cK
    zre
    cM
    cK
    ltlen
    syl2anr
    @20
    @8
    @19
    @20
    cM
    cK
    wne
    @8
    cK
    cM
    necom
    cM
    cK
    df-ne
    sylbb
    adantl
    syl6bi
    ex
    com23
    impcom
    imp
    jctird
    syl21anc
    mpd
    @3
    @4
    ioran
    sylibr
    a1i
    con2d
    impbid
end
