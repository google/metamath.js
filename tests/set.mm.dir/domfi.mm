include "cfn.mm"
include "wcel.mm"
include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "cen.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "domeng.mm"
include "ssfi.mm"
include "adantrl.mm"
include "enfii.mm"
include "adantrr.mm"
include "sylancom.mm"
include "ex.mm"
include "exlimdv.mm"
include "sylbid.mm"
include "imp.mm"

theorem domfi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. Fin /\ B ~<_ A ) -> B e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    cdom
    wbr
    #
    cB
    cfn
    wcel
    #
    @0
    @1
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
    vx
    wex
    @2
    vx
    cB
    cA
    cfn
    domeng
    @0
    @6
    @2
    vx
    @0
    @6
    @2
    @0
    @6
    @3
    cfn
    wcel
    #
    @2
    @0
    @5
    @7
    @4
    cA
    @3
    ssfi
    adantrl
    @7
    @4
    @2
    @5
    cB
    @3
    enfii
    adantrr
    sylancom
    ex
    exlimdv
    sylbid
    imp
end
