include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "simpr.mm"
include "simpl.mm"
include "cbs.mm"
include "eqid.mm"
include "cntzssv.mm"
include "syl6ss.mm"
include "cntz2ss.mm"
include "sylancom.mm"
include "sstrd.mm"

theorem cntzidss
  let cS: class S
  let cT: class T
  let cG: class G
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cH: class H
  let cY: class Y
  assume cntzmhm.z: |- Z = ( Cntz ` G )


  assert |- ( ( S C_ ( Z ` S ) /\ T C_ S ) -> T C_ ( Z ` T ) )

  proof
    cS
    cS
    cZ
    cfv
    #
    wss
    #
    cT
    cS
    wss
    #
    wa
    #
    cT
    cS
    cT
    cZ
    cfv
    #
    @1
    @2
    simpr
    @3
    cS
    @0
    @4
    @1
    @2
    simpl
    #
    @1
    @2
    cS
    cG
    cbs
    cfv
    #
    wss
    @0
    @4
    wss
    @3
    cS
    @0
    @6
    @5
    @6
    cS
    cG
    cZ
    @6
    eqid
    #
    cntzmhm.z
    cntzssv
    syl6ss
    @6
    cS
    cT
    cG
    cZ
    @7
    cntzmhm.z
    cntz2ss
    sylancom
    sstrd
    sstrd
end
