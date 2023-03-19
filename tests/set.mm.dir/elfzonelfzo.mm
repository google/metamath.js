include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "elfzo2.mm"
include "cle.mm"
include "simpr.mm"
include "eluzelz.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "cr.mm"
include "wb.mm"
include "eluzelre.mm"
include "zre.mm"
include "ltnle.mm"
include "syl2an.mm"
include "id.mm"
include "3expa.mm"
include "sylibr.mm"
include "ex.mm"
include "sylbird.mm"
include "con1d.mm"
include "com23.mm"
include "imp31.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "simpll2.mm"
include "simpll3.mm"
include "sylanb.mm"
include "com12.mm"

theorem elfzonelfzo
  let cR: class R
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( N e. ZZ -> ( ( K e. ( M ..^ R ) /\ -. K e. ( M ..^ N ) ) -> K e. ( N ..^ R ) ) )

  proof
    cK
    cM
    cR
    cfzo
    co
    wcel
    #
    cK
    cM
    cN
    cfzo
    co
    wcel
    #
    wn
    #
    wa
    cN
    cz
    wcel
    #
    cK
    cN
    cR
    cfzo
    co
    wcel
    #
    @0
    cK
    cM
    cuz
    cfv
    wcel
    #
    cR
    cz
    wcel
    #
    cK
    cR
    clt
    wbr
    #
    w3a
    #
    @2
    @3
    @4
    wi
    cK
    cM
    cR
    elfzo2
    @8
    @2
    wa
    #
    @3
    @4
    @9
    @3
    wa
    #
    cK
    cN
    cuz
    cfv
    wcel
    #
    @6
    @7
    @4
    @10
    @3
    cK
    cz
    wcel
    #
    cN
    cK
    cle
    wbr
    #
    @11
    @9
    @3
    simpr
    @8
    @12
    @2
    @3
    @5
    @6
    @12
    @7
    cM
    cK
    eluzelz
    3ad2ant1
    ad2antrr
    @8
    @2
    @3
    @13
    @5
    @6
    @2
    @3
    @13
    wi
    wi
    @7
    @5
    @3
    @2
    @13
    @5
    @3
    @2
    @13
    wi
    @5
    @3
    wa
    #
    @13
    @1
    @14
    @13
    wn
    #
    cK
    cN
    clt
    wbr
    #
    @1
    @5
    cK
    cr
    wcel
    cN
    cr
    wcel
    @16
    @15
    wb
    @3
    cM
    cK
    eluzelre
    cN
    zre
    cK
    cN
    ltnle
    syl2an
    @14
    @16
    @1
    @14
    @16
    wa
    @5
    @3
    @16
    w3a
    #
    @1
    @5
    @3
    @16
    @17
    @17
    id
    3expa
    cK
    cM
    cN
    elfzo2
    sylibr
    ex
    sylbird
    con1d
    ex
    com23
    3ad2ant1
    imp31
    cN
    cK
    eluz2
    syl3anbrc
    @5
    @6
    @7
    @2
    @3
    simpll2
    @5
    @6
    @7
    @2
    @3
    simpll3
    cK
    cN
    cR
    elfzo2
    syl3anbrc
    ex
    sylanb
    com12
end
