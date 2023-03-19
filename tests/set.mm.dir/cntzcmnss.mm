include "cfv.mm"
include "wceq.mm"
include "ccmn.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cntzcmn.mm"
include "wb.mm"
include "sseq2.mm"
include "eqcoms.mm"
include "biimpd.mm"
include "adantld.mm"
include "mpcom.mm"

theorem cntzcmnss
  let cB: class B
  let cS: class S
  let cG: class G
  let cZ: class Z
  assume cntzcmnss.b: |- B = ( Base ` G )
  assume cntzcmnss.z: |- Z = ( Cntz ` G )


  assert |- ( ( G e. CMnd /\ S C_ B ) -> S C_ ( Z ` S ) )

  proof
    cS
    cZ
    cfv
    #
    cB
    wceq
    #
    cG
    ccmn
    wcel
    #
    cS
    cB
    wss
    #
    wa
    cS
    @0
    wss
    #
    cB
    cS
    cG
    cZ
    cntzcmnss.b
    cntzcmnss.z
    cntzcmn
    @1
    @3
    @4
    @2
    @1
    @3
    @4
    @3
    @4
    wb
    cB
    @0
    cB
    @0
    cS
    sseq2
    eqcoms
    biimpd
    adantld
    mpcom
end
