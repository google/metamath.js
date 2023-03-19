include "cfin4.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wex.mm"
include "domeng.mm"
include "biimpa.mm"
include "ensym.mm"
include "ad2antrl.mm"
include "ssfin4.mm"
include "ad2ant2rl.mm"
include "fin4en1.mm"
include "sylc.mm"
include "exlimddv.mm"

theorem domfin4
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vf: setvar f
  let vx: setvar x


  assert |- ( ( A e. Fin4 /\ B ~<_ A ) -> B e. Fin4 )

  proof
    cA
    cfin4
    wcel
    #
    cB
    cA
    cdom
    wbr
    #
    wa
    #
    cB
    vx
    cv
    #
    cen
    wbr
    #
    @3
    cA
    wss
    #
    wa
    #
    cB
    cfin4
    wcel
    #
    vx
    @0
    @1
    @6
    vx
    wex
    vx
    cB
    cA
    cfin4
    domeng
    biimpa
    @2
    @6
    wa
    @3
    cB
    cen
    wbr
    #
    @3
    cfin4
    wcel
    #
    @7
    @4
    @8
    @2
    @5
    cB
    @3
    ensym
    ad2antrl
    @0
    @5
    @9
    @1
    @4
    cA
    @3
    ssfin4
    ad2ant2rl
    @3
    cB
    fin4en1
    sylc
    exlimddv
end
