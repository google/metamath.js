include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "cdom.mm"
include "wbr.mm"
include "cpw.mm"
include "csdm.mm"
include "cen.mm"
include "simprl.mm"
include "gchi.mm"
include "3com23.mm"
include "3expia.mm"
include "con3dimp.mm"
include "an32s.mm"
include "adantrl.mm"
include "bren2.mm"
include "sylanbrc.mm"

theorem gchen1
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. GCH /\ -. A e. Fin ) /\ ( A ~<_ B /\ B ~< ~P A ) ) -> A ~~ B )

  proof
    cA
    cgch
    wcel
    #
    cA
    cfn
    wcel
    #
    wn
    #
    wa
    #
    cA
    cB
    cdom
    wbr
    #
    cB
    cA
    cpw
    csdm
    wbr
    #
    wa
    wa
    @4
    cA
    cB
    csdm
    wbr
    #
    wn
    #
    cA
    cB
    cen
    wbr
    @3
    @4
    @5
    simprl
    @3
    @5
    @7
    @4
    @0
    @5
    @2
    @7
    @0
    @5
    wa
    @6
    @1
    @0
    @5
    @6
    @1
    @0
    @6
    @5
    @1
    cA
    cB
    gchi
    3com23
    3expia
    con3dimp
    an32s
    adantrl
    cA
    cB
    bren2
    sylanbrc
end
