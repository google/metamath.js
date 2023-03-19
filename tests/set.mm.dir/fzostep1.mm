include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wo.mm"
include "cz.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "elfzoel1.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzoss1.mm"
include "4syl.mm"
include "1z.mm"
include "fzoaddel.mm"
include "mpan2.mm"
include "sseldd.mm"
include "wb.mm"
include "cle.mm"
include "wbr.mm"
include "elfzoel2.mm"
include "clt.mm"
include "elfzolt3.mm"
include "wi.mm"
include "cr.mm"
include "zre.mm"
include "ltle.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpd.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzosplitsni.mm"
include "syl.mm"
include "mpbid.mm"

theorem fzostep1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B ..^ C ) -> ( ( A + 1 ) e. ( B ..^ C ) \/ ( A + 1 ) = C ) )

  proof
    cA
    cB
    cC
    cfzo
    co
    #
    wcel
    #
    cA
    c1
    caddc
    co
    #
    cB
    cC
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    @2
    @0
    wcel
    @2
    cC
    wceq
    wo
    #
    @1
    cB
    c1
    caddc
    co
    #
    @3
    cfzo
    co
    #
    @4
    @2
    @1
    cB
    cz
    wcel
    #
    cB
    cB
    cuz
    cfv
    #
    wcel
    @7
    @10
    wcel
    @8
    @4
    wss
    cA
    cB
    cC
    elfzoel1
    #
    cB
    uzid
    cB
    cB
    peano2uz
    @7
    cB
    @3
    fzoss1
    4syl
    @1
    c1
    cz
    wcel
    @2
    @8
    wcel
    1z
    cA
    cB
    cC
    c1
    fzoaddel
    mpan2
    sseldd
    @1
    cC
    @10
    wcel
    #
    @5
    @6
    wb
    @1
    @9
    cC
    cz
    wcel
    #
    cB
    cC
    cle
    wbr
    #
    @12
    @11
    cA
    cB
    cC
    elfzoel2
    #
    @1
    cB
    cC
    clt
    wbr
    #
    @14
    cA
    cB
    cC
    elfzolt3
    @1
    @9
    @13
    @16
    @14
    wi
    #
    @11
    @15
    @9
    cB
    cr
    wcel
    cC
    cr
    wcel
    @17
    @13
    cB
    zre
    cC
    zre
    cB
    cC
    ltle
    syl2an
    syl2anc
    mpd
    cB
    cC
    eluz2
    syl3anbrc
    cB
    cC
    @2
    fzosplitsni
    syl
    mpbid
end
