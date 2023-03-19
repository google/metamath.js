include "cpjh.mm"
include "cfv.mm"
include "cin.mm"
include "ccom.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "chincli.mm"
include "pjss1coi.mm"
include "mpbi.mm"
include "eqcomi.mm"

theorem pjin1i
  let cG: class G
  let cH: class H
  assume pjin1.1: |- G e. CH
  assume pjin1.2: |- H e. CH


  assert |- ( projh ` ( G i^i H ) ) = ( ( projh ` G ) o. ( projh ` ( G i^i H ) ) )

  proof
    cG
    cpjh
    cfv
    cG
    cH
    cin
    #
    cpjh
    cfv
    #
    ccom
    #
    @1
    @0
    cG
    wss
    @2
    @1
    wceq
    cG
    cH
    inss1
    @0
    cG
    cG
    cH
    pjin1.1
    pjin1.2
    chincli
    pjin1.1
    pjss1coi
    mpbi
    eqcomi
end
