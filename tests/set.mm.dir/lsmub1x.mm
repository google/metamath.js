include "wss.mm"
include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "c0g.mm"
include "cplusg.mm"
include "cmnd.mm"
include "wceq.mm"
include "submrcl.mm"
include "ad2antlr.mm"
include "simpll.mm"
include "simpr.mm"
include "sseldd.mm"
include "eqid.mm"
include "mndrid.mm"
include "syl2anc.mm"
include "submss.mm"
include "subm0cl.mm"
include "lsmelvalix.mm"
include "syl32anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem lsmub1x
  let cB: class B
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cV: class V
  assume lsmless2.v: |- B = ( Base ` G )
  assume lsmless2.s: |- .(+) = ( LSSum ` G )


  assert |- ( ( T C_ B /\ U e. ( SubMnd ` G ) ) -> T C_ ( T .(+) U ) )

  proof
    cT
    cB
    wss
    #
    cU
    cG
    csubmnd
    cfv
    wcel
    #
    wa
    #
    vx
    cT
    cT
    cU
    c.po
    co
    #
    @2
    vx
    cv
    #
    cT
    wcel
    #
    @4
    @3
    wcel
    @2
    @5
    wa
    #
    @4
    cG
    c0g
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @4
    @3
    @6
    cG
    cmnd
    wcel
    #
    @4
    cB
    wcel
    @9
    @4
    wceq
    @1
    @10
    @0
    @5
    cU
    cG
    submrcl
    ad2antlr
    #
    @6
    cT
    cB
    @4
    @0
    @1
    @5
    simpll
    #
    @2
    @5
    simpr
    #
    sseldd
    cB
    @8
    cG
    @4
    @7
    lsmless2.v
    @8
    eqid
    #
    @7
    eqid
    #
    mndrid
    syl2anc
    @6
    @10
    @0
    cU
    cB
    wss
    #
    @5
    @7
    cU
    wcel
    #
    @9
    @3
    wcel
    @11
    @12
    @1
    @16
    @0
    @5
    cB
    cU
    cG
    lsmless2.v
    submss
    ad2antlr
    @13
    @1
    @17
    @0
    @5
    cU
    cG
    @7
    @15
    subm0cl
    ad2antlr
    cB
    @8
    c.po
    cT
    cU
    cG
    cmnd
    @4
    @7
    lsmless2.v
    @14
    lsmless2.s
    lsmelvalix
    syl32anc
    eqeltrrd
    ex
    ssrdv
end
