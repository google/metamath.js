include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cfz.mm"
include "ancom.mm"
include "wb.mm"
include "cr.mm"
include "zre.mm"
include "suble.mm"
include "syl3an.mm"
include "3comr.mm"
include "3expb.mm"
include "adantll.mm"
include "lesub.mm"
include "adantlr.mm"
include "anbi12d.mm"
include "syl5rbbr.mm"
include "simprr.mm"
include "zsubcl.mm"
include "ancoms.mm"
include "ad2ant2lr.mm"
include "ad2ant2r.mm"
include "elfz.mm"
include "syl3anc.mm"
include "adantl.mm"
include "simpll.mm"
include "simplr.mm"
include "3bitr4d.mm"

theorem fzrev
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ ( J e. ZZ /\ K e. ZZ ) ) -> ( K e. ( ( J - N ) ... ( J - M ) ) <-> ( J - K ) e. ( M ... N ) ) )

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
    cJ
    cN
    cmin
    co
    #
    cK
    cle
    wbr
    #
    cK
    cJ
    cM
    cmin
    co
    #
    cle
    wbr
    #
    wa
    #
    cM
    cJ
    cK
    cmin
    co
    #
    cle
    wbr
    #
    @12
    cN
    cle
    wbr
    #
    wa
    #
    cK
    @7
    @9
    cfz
    co
    wcel
    #
    @12
    cM
    cN
    cfz
    co
    wcel
    #
    @15
    @14
    @13
    wa
    @6
    @11
    @14
    @13
    ancom
    @6
    @14
    @8
    @13
    @10
    @1
    @5
    @14
    @8
    wb
    #
    @0
    @1
    @3
    @4
    @18
    @3
    @4
    @1
    @18
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
    @1
    cN
    cr
    wcel
    @18
    cJ
    zre
    #
    cK
    zre
    #
    cN
    zre
    cJ
    cK
    cN
    suble
    syl3an
    3comr
    3expb
    adantll
    @0
    @5
    @13
    @10
    wb
    #
    @1
    @0
    @3
    @4
    @23
    @0
    cM
    cr
    wcel
    @3
    @19
    @4
    @20
    @23
    cM
    zre
    @21
    @22
    cM
    cJ
    cK
    lesub
    syl3an
    3expb
    adantlr
    anbi12d
    syl5rbbr
    @6
    @4
    @7
    cz
    wcel
    #
    @9
    cz
    wcel
    #
    @16
    @11
    wb
    @2
    @3
    @4
    simprr
    @1
    @3
    @24
    @0
    @4
    @3
    @1
    @24
    cJ
    cN
    zsubcl
    ancoms
    ad2ant2lr
    @0
    @3
    @25
    @1
    @4
    @3
    @0
    @25
    cJ
    cM
    zsubcl
    ancoms
    ad2ant2r
    cK
    @7
    @9
    elfz
    syl3anc
    @6
    @12
    cz
    wcel
    #
    @0
    @1
    @17
    @15
    wb
    @5
    @26
    @2
    cJ
    cK
    zsubcl
    adantl
    @0
    @1
    @5
    simpll
    @0
    @1
    @5
    simplr
    @12
    cM
    cN
    elfz
    syl3anc
    3bitr4d
end
