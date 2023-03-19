include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wb.mm"
include "simpl.mm"
include "zaddcl.mm"
include "2thd.mm"
include "adantl.mm"
include "cr.mm"
include "zre.mm"
include "leadd1.mm"
include "syl3an.mm"
include "3expb.mm"
include "adantlr.mm"
include "3com12.mm"
include "adantll.mm"
include "3anbi123d.mm"
include "elfz1.mm"
include "adantr.mm"
include "syl2an.mm"
include "anandirs.mm"
include "adantrl.mm"
include "3bitr4d.mm"

theorem fzaddel
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( J e. ZZ /\ K e. ZZ ) ) -> ( J e. ( M ... N ) <-> ( J + K ) e. ( ( M + K ) ... ( N + K ) ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cJ
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    wa
    #
    @3
    cM
    cJ
    cle
    wbr
    #
    cJ
    cN
    cle
    wbr
    #
    w3a
    #
    cJ
    cK
    caddc
    co
    #
    cz
    wcel
    #
    cM
    cK
    caddc
    co
    #
    @10
    cle
    wbr
    #
    @10
    cN
    cK
    caddc
    co
    #
    cle
    wbr
    #
    w3a
    #
    cJ
    cM
    cN
    cfz
    co
    wcel
    #
    @10
    @12
    @14
    cfz
    co
    wcel
    #
    @6
    @3
    @11
    @7
    @13
    @8
    @15
    @5
    @3
    @11
    wb
    @2
    @5
    @3
    @11
    @3
    @4
    simpl
    cJ
    cK
    zaddcl
    2thd
    adantl
    @0
    @5
    @7
    @13
    wb
    #
    @1
    @0
    @3
    @4
    @19
    @0
    cM
    cr
    wcel
    @3
    cJ
    cr
    wcel
    #
    @4
    cK
    cr
    wcel
    #
    @19
    cM
    zre
    cJ
    zre
    #
    cK
    zre
    #
    cM
    cJ
    cK
    leadd1
    syl3an
    3expb
    adantlr
    @1
    @5
    @8
    @15
    wb
    #
    @0
    @1
    @3
    @4
    @24
    @3
    @1
    @4
    @24
    @3
    @20
    @1
    cN
    cr
    wcel
    @4
    @21
    @24
    @22
    cN
    zre
    @23
    cJ
    cN
    cK
    leadd1
    syl3an
    3com12
    3expb
    adantll
    3anbi123d
    @2
    @17
    @9
    wb
    @5
    cJ
    cM
    cN
    elfz1
    adantr
    @2
    @4
    @18
    @16
    wb
    #
    @3
    @0
    @1
    @4
    @25
    @0
    @4
    wa
    @12
    cz
    wcel
    @14
    cz
    wcel
    @25
    @1
    @4
    wa
    cM
    cK
    zaddcl
    cN
    cK
    zaddcl
    @10
    @12
    @14
    elfz1
    syl2an
    anandirs
    adantrl
    3bitr4d
end
