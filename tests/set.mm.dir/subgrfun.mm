include "csubgr.mm"
include "wbr.mm"
include "ciedg.mm"
include "cfv.mm"
include "wfun.mm"
include "cvtx.mm"
include "wss.mm"
include "cedg.mm"
include "cpw.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "subgrprop2.mm"
include "funss.mm"
include "3ad2ant2.mm"
include "syl.mm"
include "impcom.mm"

theorem subgrfun
  let cS: class S
  let cG: class G


  assert |- ( ( Fun ( iEdg ` G ) /\ S SubGraph G ) -> Fun ( iEdg ` S ) )

  proof
    cS
    cG
    csubgr
    wbr
    #
    cG
    ciedg
    cfv
    #
    wfun
    #
    cS
    ciedg
    cfv
    #
    wfun
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
    @3
    @1
    wss
    #
    cS
    cedg
    cfv
    #
    @5
    cpw
    wss
    #
    w3a
    @2
    @4
    wi
    #
    @6
    @1
    cS
    @9
    cG
    @3
    @5
    @5
    eqid
    @6
    eqid
    @3
    eqid
    @1
    eqid
    @9
    eqid
    subgrprop2
    @8
    @7
    @11
    @10
    @3
    @1
    funss
    3ad2ant2
    syl
    impcom
end
