include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cz.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wss.mm"
include "cle.mm"
include "wa.mm"
include "wi.mm"
include "fzolb2.mm"
include "biimp3ar.mm"
include "c1.mm"
include "cmin.mm"
include "fzoend.mm"
include "ssel2.mm"
include "elfzolt2.mm"
include "wb.mm"
include "simp2.mm"
include "elfzoel2.mm"
include "zlem1lt.mm"
include "syl2anr.mm"
include "elfzole1.mm"
include "pm3.2.mm"
include "syl.mm"
include "adantr.mm"
include "sylbird.mm"
include "ex.mm"
include "com13.mm"
include "3syl.mm"
include "com24.mm"
include "syl5com.mm"
include "pm2.43a.mm"
include "com14.mm"
include "mpcom.mm"

theorem ssfzo12
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ L e. ZZ /\ K < L ) -> ( ( K ..^ L ) C_ ( M ..^ N ) -> ( M <_ K /\ L <_ N ) ) )

  proof
    cK
    cK
    cL
    cfzo
    co
    #
    wcel
    #
    cK
    cz
    wcel
    #
    cL
    cz
    wcel
    #
    cK
    cL
    clt
    wbr
    #
    w3a
    #
    @0
    cM
    cN
    cfzo
    co
    #
    wss
    #
    cM
    cK
    cle
    wbr
    #
    cL
    cN
    cle
    wbr
    #
    wa
    #
    wi
    #
    @2
    @3
    @1
    @4
    cK
    cL
    fzolb2
    biimp3ar
    cL
    c1
    cmin
    co
    #
    @0
    wcel
    #
    @1
    @5
    @11
    wi
    cK
    cL
    fzoend
    @7
    @1
    @5
    @13
    @10
    @1
    @7
    @5
    @13
    @10
    wi
    wi
    #
    @7
    @1
    @7
    @14
    wi
    @7
    @1
    wa
    cK
    @6
    wcel
    #
    @7
    @14
    @0
    @6
    cK
    ssel2
    @7
    @13
    @5
    @15
    @10
    @7
    @13
    @5
    @15
    @10
    wi
    wi
    #
    @7
    @13
    wa
    @12
    @6
    wcel
    @12
    cN
    clt
    wbr
    #
    @16
    @0
    @6
    @12
    ssel2
    @12
    cM
    cN
    elfzolt2
    @15
    @5
    @17
    @10
    @15
    @5
    @17
    @10
    wi
    @15
    @5
    wa
    @17
    @9
    @10
    @5
    @3
    cN
    cz
    wcel
    @9
    @17
    wb
    @15
    @2
    @3
    @4
    simp2
    cK
    cM
    cN
    elfzoel2
    cL
    cN
    zlem1lt
    syl2anr
    @15
    @9
    @10
    wi
    #
    @5
    @15
    @8
    @18
    cK
    cM
    cN
    elfzole1
    @8
    @9
    pm3.2
    syl
    adantr
    sylbird
    ex
    com13
    3syl
    ex
    com24
    syl5com
    ex
    pm2.43a
    com14
    mpcom
    mpcom
end
