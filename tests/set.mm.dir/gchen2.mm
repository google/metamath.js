include "cgch.mm"
include "wcel.mm"
include "cfn.mm"
include "wn.mm"
include "wa.mm"
include "csdm.mm"
include "wbr.mm"
include "cpw.mm"
include "cdom.mm"
include "cen.mm"
include "simprr.mm"
include "gchi.mm"
include "3expia.mm"
include "con3dimp.mm"
include "an32s.mm"
include "adantrr.mm"
include "bren2.mm"
include "sylanbrc.mm"

theorem gchen2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. GCH /\ -. A e. Fin ) /\ ( A ~< B /\ B ~<_ ~P A ) ) -> B ~~ ~P A )

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
    csdm
    wbr
    #
    cB
    cA
    cpw
    #
    cdom
    wbr
    #
    wa
    wa
    @6
    cB
    @5
    csdm
    wbr
    #
    wn
    #
    cB
    @5
    cen
    wbr
    @3
    @4
    @6
    simprr
    @3
    @4
    @8
    @6
    @0
    @4
    @2
    @8
    @0
    @4
    wa
    @7
    @1
    @0
    @4
    @7
    @1
    cA
    cB
    gchi
    3expia
    con3dimp
    an32s
    adantrr
    cB
    @5
    bren2
    sylanbrc
end
