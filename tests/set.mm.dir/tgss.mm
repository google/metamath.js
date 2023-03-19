include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ctg.mm"
include "cfv.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wi.mm"
include "ssrin.mm"
include "unissd.mm"
include "sstr2.mm"
include "syl5com.mm"
include "adantl.mm"
include "cvv.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "eltg.mm"
include "syl.mm"
include "adantr.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem tgss
  let cB: class B
  let cC: class C
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J


  assert |- ( ( C e. V /\ B C_ C ) -> ( topGen ` B ) C_ ( topGen ` C ) )

  proof
    cC
    cV
    wcel
    #
    cB
    cC
    wss
    #
    wa
    #
    vx
    cB
    ctg
    cfv
    #
    cC
    ctg
    cfv
    #
    @2
    vx
    cv
    #
    cB
    @5
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    @5
    cC
    @6
    cin
    #
    cuni
    #
    wss
    #
    @5
    @3
    wcel
    #
    @5
    @4
    wcel
    #
    @1
    @9
    @12
    wi
    @0
    @1
    @8
    @11
    wss
    @9
    @12
    @1
    @7
    @10
    cB
    cC
    @6
    ssrin
    unissd
    @5
    @8
    @11
    sstr2
    syl5com
    adantl
    @2
    cB
    cvv
    wcel
    #
    @13
    @9
    wb
    @1
    @0
    @15
    cB
    cC
    cV
    ssexg
    ancoms
    @5
    cB
    cvv
    eltg
    syl
    @0
    @14
    @12
    wb
    @1
    @5
    cC
    cV
    eltg
    adantr
    3imtr4d
    ssrdv
end
