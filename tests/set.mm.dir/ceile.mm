include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cfl.mm"
include "cfv.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "ceim1l.mm"
include "adantr.mm"
include "wi.mm"
include "ceicl.mm"
include "zre.mm"
include "peano2rem.mm"
include "3syl.mm"
include "simpl.mm"
include "adantl.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "wb.mm"
include "zlem1lt.mm"
include "sylan.mm"
include "sylibrd.mm"
include "3impia.mm"

theorem ceile
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. ZZ /\ A <_ B ) -> -u ( |_ ` -u A ) <_ B )

  proof
    cA
    cr
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cneg
    cfl
    cfv
    cneg
    #
    cB
    cle
    wbr
    #
    @0
    @1
    wa
    #
    @2
    @3
    c1
    cmin
    co
    #
    cB
    clt
    wbr
    #
    @4
    @5
    @6
    cA
    clt
    wbr
    #
    @2
    @7
    @0
    @8
    @1
    cA
    ceim1l
    adantr
    @5
    @6
    cr
    wcel
    #
    @0
    cB
    cr
    wcel
    #
    @8
    @2
    wa
    @7
    wi
    @0
    @9
    @1
    @0
    @3
    cz
    wcel
    #
    @3
    cr
    wcel
    @9
    cA
    ceicl
    #
    @3
    zre
    @3
    peano2rem
    3syl
    adantr
    @0
    @1
    simpl
    @1
    @10
    @0
    cB
    zre
    adantl
    @6
    cA
    cB
    ltletr
    syl3anc
    mpand
    @0
    @11
    @1
    @4
    @7
    wb
    @12
    @3
    cB
    zlem1lt
    sylan
    sylibrd
    3impia
end
