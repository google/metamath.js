include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "simplr.mm"
include "recnd.mm"
include "simpll.mm"
include "abscl.mm"
include "syl.mm"
include "simpr.mm"
include "cle.mm"
include "leabs.mm"
include "ltletrd.mm"
include "gtned.mm"
include "fveq2.mm"
include "necon3i.mm"
include "subne0d.mm"
include "3impa.mm"

theorem abssubne0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. RR /\ ( abs ` A ) < B ) -> ( B - A ) =/= 0 )

  proof
    cA
    cc
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    cB
    cA
    cmin
    co
    cc0
    wne
    @0
    @1
    wa
    #
    @3
    wa
    #
    cB
    cA
    @5
    cB
    @0
    @1
    @3
    simplr
    #
    recnd
    #
    @0
    @1
    @3
    simpll
    #
    @5
    cB
    cabs
    cfv
    #
    @2
    wne
    cB
    cA
    wne
    @5
    @2
    @9
    @5
    @0
    @2
    cr
    wcel
    @8
    cA
    abscl
    syl
    #
    @5
    @2
    cB
    @9
    @10
    @6
    @5
    cB
    cc
    wcel
    @9
    cr
    wcel
    @7
    cB
    abscl
    syl
    @4
    @3
    simpr
    @5
    @1
    cB
    @9
    cle
    wbr
    @6
    cB
    leabs
    syl
    ltletrd
    gtned
    cB
    cA
    @9
    @2
    cB
    cA
    cabs
    fveq2
    necon3i
    syl
    subne0d
    3impa
end
