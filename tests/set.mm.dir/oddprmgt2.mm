include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "eldifsn.mm"
include "cuz.mm"
include "cfv.mm"
include "wi.mm"
include "prmuz2.mm"
include "cz.mm"
include "cle.mm"
include "w3a.mm"
include "eluz2.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "ltlen.mm"
include "syl2an.mm"
include "biimprd.mm"
include "exp4b.mm"
include "3imp.mm"
include "sylbi.mm"
include "syl.mm"
include "imp.mm"

theorem oddprmgt2
  let cP: class P


  assert |- ( P e. ( Prime \ { 2 } ) -> 2 < P )

  proof
    cP
    cprime
    c2
    csn
    cdif
    wcel
    cP
    cprime
    wcel
    #
    cP
    c2
    wne
    #
    wa
    c2
    cP
    clt
    wbr
    #
    cP
    cprime
    c2
    eldifsn
    @0
    @1
    @2
    @0
    cP
    c2
    cuz
    cfv
    wcel
    #
    @1
    @2
    wi
    #
    cP
    prmuz2
    @3
    c2
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    c2
    cP
    cle
    wbr
    #
    w3a
    @4
    c2
    cP
    eluz2
    @5
    @6
    @7
    @4
    @5
    @6
    @7
    @1
    @2
    @5
    @6
    wa
    @2
    @7
    @1
    wa
    #
    @5
    c2
    cr
    wcel
    cP
    cr
    wcel
    @2
    @8
    wb
    @6
    c2
    zre
    cP
    zre
    c2
    cP
    ltlen
    syl2an
    biimprd
    exp4b
    3imp
    sylbi
    syl
    imp
    sylbi
end
