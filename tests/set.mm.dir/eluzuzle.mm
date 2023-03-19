include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wa.mm"
include "eluz2.mm"
include "simpll.mm"
include "simpr2.mm"
include "cr.mm"
include "zre.mm"
include "ad2antrr.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "3ad2ant2.mm"
include "simplr.mm"
include "simpr3.mm"
include "letrd.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "syl5bi.mm"

theorem eluzuzle
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( B e. ZZ /\ B <_ A ) -> ( C e. ( ZZ>= ` A ) -> C e. ( ZZ>= ` B ) ) )

  proof
    cC
    cA
    cuz
    cfv
    wcel
    cA
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    w3a
    #
    cB
    cz
    wcel
    #
    cB
    cA
    cle
    wbr
    #
    wa
    #
    cC
    cB
    cuz
    cfv
    wcel
    #
    cA
    cC
    eluz2
    @6
    @3
    @7
    @6
    @3
    wa
    #
    @4
    @1
    cB
    cC
    cle
    wbr
    @7
    @4
    @5
    @3
    simpll
    @6
    @0
    @1
    @2
    simpr2
    @8
    cB
    cA
    cC
    @4
    cB
    cr
    wcel
    @5
    @3
    cB
    zre
    ad2antrr
    @3
    cA
    cr
    wcel
    #
    @6
    @0
    @1
    @9
    @2
    cA
    zre
    3ad2ant1
    adantl
    @3
    cC
    cr
    wcel
    #
    @6
    @1
    @0
    @10
    @2
    cC
    zre
    3ad2ant2
    adantl
    @4
    @5
    @3
    simplr
    @6
    @0
    @1
    @2
    simpr3
    letrd
    cB
    cC
    eluz2
    syl3anbrc
    ex
    syl5bi
end
