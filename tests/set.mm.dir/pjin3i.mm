include "wss.mm"
include "wa.mm"
include "cin.mm"
include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "ssin.mm"
include "pjss2coi.mm"
include "eqcom.mm"
include "bitri.mm"
include "anbi12i.mm"
include "chincli.mm"
include "3bitr3i.mm"

theorem pjin3i
  let cF: class F
  let cG: class G
  let cH: class H
  assume pjin3.1: |- F e. CH
  assume pjin3.2: |- G e. CH
  assume pjin3.3: |- H e. CH


  assert |- ( ( ( projh ` F ) = ( ( projh ` F ) o. ( projh ` G ) ) /\ ( projh ` F ) = ( ( projh ` F ) o. ( projh ` H ) ) ) <-> ( projh ` F ) = ( ( projh ` F ) o. ( projh ` ( G i^i H ) ) ) )

  proof
    cF
    cG
    wss
    #
    cF
    cH
    wss
    #
    wa
    cF
    cG
    cH
    cin
    #
    wss
    #
    cF
    cpjh
    cfv
    #
    @4
    cG
    cpjh
    cfv
    ccom
    #
    wceq
    #
    @4
    @4
    cH
    cpjh
    cfv
    ccom
    #
    wceq
    #
    wa
    @4
    @4
    @2
    cpjh
    cfv
    ccom
    #
    wceq
    #
    cF
    cG
    cH
    ssin
    @0
    @6
    @1
    @8
    @0
    @5
    @4
    wceq
    @6
    cF
    cG
    pjin3.1
    pjin3.2
    pjss2coi
    @5
    @4
    eqcom
    bitri
    @1
    @7
    @4
    wceq
    @8
    cF
    cH
    pjin3.1
    pjin3.3
    pjss2coi
    @7
    @4
    eqcom
    bitri
    anbi12i
    @3
    @9
    @4
    wceq
    @10
    cF
    @2
    pjin3.1
    cG
    cH
    pjin3.2
    pjin3.3
    chincli
    pjss2coi
    @9
    @4
    eqcom
    bitri
    3bitr3i
end
