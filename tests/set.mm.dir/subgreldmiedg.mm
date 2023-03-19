include "csubgr.mm"
include "wbr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cvtx.mm"
include "wss.mm"
include "cedg.mm"
include "cpw.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "subgrprop2.mm"
include "dmss.mm"
include "3ad2ant2.mm"
include "sseld.mm"
include "syl.mm"
include "imp.mm"

theorem subgreldmiedg
  let cS: class S
  let cG: class G
  let cX: class X


  assert |- ( ( S SubGraph G /\ X e. dom ( iEdg ` S ) ) -> X e. dom ( iEdg ` G ) )

  proof
    cS
    cG
    csubgr
    wbr
    #
    cX
    cS
    ciedg
    cfv
    #
    cdm
    #
    wcel
    #
    cX
    cG
    ciedg
    cfv
    #
    cdm
    #
    wcel
    #
    @0
    cS
    cvtx
    cfv
    #
    cG
    cvtx
    cfv
    #
    wss
    #
    @1
    @4
    wss
    #
    cS
    cedg
    cfv
    #
    @7
    cpw
    wss
    #
    w3a
    #
    @3
    @6
    wi
    @8
    @4
    cS
    @11
    cG
    @1
    @7
    @7
    eqid
    @8
    eqid
    @1
    eqid
    @4
    eqid
    @11
    eqid
    subgrprop2
    @13
    @2
    @5
    cX
    @10
    @9
    @2
    @5
    wss
    @12
    @1
    @4
    dmss
    3ad2ant2
    sseld
    syl
    imp
end
