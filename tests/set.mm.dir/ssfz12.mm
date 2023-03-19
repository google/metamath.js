include "cz.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cfz.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "cuz.mm"
include "cfv.mm"
include "eluz.mm"
include "biimp3ar.mm"
include "eluzfz1.mm"
include "syl.mm"
include "eluzfz2.mm"
include "ssel2.mm"
include "elfzuz3.mm"
include "eluz2.mm"
include "pm3.21.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "a1i.mm"
include "com13.mm"
include "elfzuz.mm"
include "syl11.mm"
include "3syl.mm"
include "ex.mm"
include "com4t.mm"
include "com24.mm"
include "pm2.43i.mm"
include "com14.mm"
include "mpcom.mm"
include "mpd.mm"

theorem ssfz12
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( K e. ZZ /\ L e. ZZ /\ K <_ L ) -> ( ( K ... L ) C_ ( M ... N ) -> ( M <_ K /\ L <_ N ) ) )

  proof
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
    cle
    wbr
    #
    w3a
    #
    cK
    cK
    cL
    cfz
    co
    #
    wcel
    #
    @4
    cM
    cN
    cfz
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
    @3
    cL
    cK
    cuz
    cfv
    wcel
    #
    @5
    @0
    @1
    @12
    @2
    cK
    cL
    eluz
    biimp3ar
    #
    cK
    cL
    eluzfz1
    syl
    cL
    @4
    wcel
    #
    @3
    @5
    @11
    wi
    @3
    @12
    @14
    @13
    cK
    cL
    eluzfz2
    syl
    @7
    @3
    @5
    @14
    @10
    @7
    @3
    @5
    @14
    @10
    wi
    #
    wi
    wi
    @7
    @5
    @3
    @7
    @15
    @7
    @5
    @3
    @7
    @15
    wi
    wi
    #
    @7
    @5
    wa
    cK
    @6
    wcel
    #
    @16
    @4
    @6
    cK
    ssel2
    @7
    @14
    @17
    @3
    @10
    @7
    @14
    @17
    @3
    @10
    wi
    #
    wi
    #
    @7
    @14
    wa
    cL
    @6
    wcel
    cN
    cL
    cuz
    cfv
    wcel
    #
    @19
    @4
    @6
    cL
    ssel2
    cL
    cM
    cN
    elfzuz3
    cK
    cM
    cuz
    cfv
    wcel
    #
    @20
    @18
    @17
    @21
    cM
    cz
    wcel
    #
    @0
    @8
    w3a
    @20
    @18
    wi
    #
    cM
    cK
    eluz2
    @8
    @22
    @23
    @0
    @3
    @20
    @8
    @10
    @20
    @8
    @10
    wi
    #
    wi
    @3
    @20
    @1
    cN
    cz
    wcel
    #
    @9
    w3a
    @24
    cL
    cN
    eluz2
    @9
    @1
    @24
    @25
    @9
    @8
    pm3.21
    3ad2ant3
    sylbi
    a1i
    com13
    3ad2ant3
    sylbi
    cK
    cM
    cN
    elfzuz
    syl11
    3syl
    ex
    com4t
    syl
    ex
    com24
    pm2.43i
    com14
    mpcom
    mpd
end
