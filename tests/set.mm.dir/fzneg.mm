include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cfz.mm"
include "co.mm"
include "ancom.mm"
include "cr.mm"
include "zre.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "lenegd.mm"
include "3ad2ant2.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "elfz.mm"
include "wb.mm"
include "znegcl.mm"
include "syl3an.mm"
include "3com23.mm"
include "3bitr4d.mm"

theorem fzneg
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A e. ( B ... C ) <-> -u A e. ( -u C ... -u B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cB
    cA
    cle
    wbr
    #
    cA
    cC
    cle
    wbr
    #
    wa
    #
    cC
    cneg
    #
    cA
    cneg
    #
    cle
    wbr
    #
    @8
    cB
    cneg
    #
    cle
    wbr
    #
    wa
    #
    cA
    cB
    cC
    cfz
    co
    wcel
    @8
    @7
    @10
    cfz
    co
    wcel
    #
    @6
    @5
    @4
    wa
    @3
    @12
    @4
    @5
    ancom
    @3
    @5
    @9
    @4
    @11
    @3
    cA
    cC
    @0
    @1
    cA
    cr
    wcel
    @2
    cA
    zre
    3ad2ant1
    #
    @2
    @0
    cC
    cr
    wcel
    @1
    cC
    zre
    3ad2ant3
    lenegd
    @3
    cB
    cA
    @1
    @0
    cB
    cr
    wcel
    @2
    cB
    zre
    3ad2ant2
    @14
    lenegd
    anbi12d
    syl5bb
    cA
    cB
    cC
    elfz
    @0
    @2
    @1
    @13
    @12
    wb
    #
    @0
    @8
    cz
    wcel
    @2
    @7
    cz
    wcel
    @1
    @10
    cz
    wcel
    @15
    cA
    znegcl
    cC
    znegcl
    cB
    znegcl
    @8
    @7
    @10
    elfz
    syl3an
    3com23
    3bitr4d
end
