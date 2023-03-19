include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "c0g.mm"
include "cplusg.mm"
include "cmnd.mm"
include "wceq.mm"
include "submrcl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "sselda.mm"
include "eqid.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "submss.mm"
include "simplr.mm"
include "subm0cl.mm"
include "lsmelvalix.mm"
include "syl32anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem lsmub2x
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


  assert |- ( ( T e. ( SubMnd ` G ) /\ U C_ B ) -> U C_ ( T .(+) U ) )

  proof
    cT
    cG
    csubmnd
    cfv
    wcel
    #
    cU
    cB
    wss
    #
    wa
    #
    vx
    cU
    cT
    cU
    c.po
    co
    #
    @2
    vx
    cv
    #
    cU
    wcel
    #
    @4
    @3
    wcel
    @2
    @5
    wa
    #
    cG
    c0g
    cfv
    #
    @4
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
    @0
    @10
    @1
    @5
    cT
    cG
    submrcl
    ad2antrr
    #
    @2
    cU
    cB
    @4
    @0
    @1
    simpr
    sselda
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
    mndlid
    syl2anc
    @6
    @10
    cT
    cB
    wss
    #
    @1
    @7
    cT
    wcel
    #
    @5
    @9
    @3
    wcel
    @11
    @0
    @14
    @1
    @5
    cB
    cT
    cG
    lsmless2.v
    submss
    ad2antrr
    @0
    @1
    @5
    simplr
    @0
    @15
    @1
    @5
    cT
    cG
    @7
    @13
    subm0cl
    ad2antrr
    @2
    @5
    simpr
    cB
    @8
    c.po
    cT
    cU
    cG
    cmnd
    @7
    @4
    lsmless2.v
    @12
    lsmless2.s
    lsmelvalix
    syl32anc
    eqeltrrd
    ex
    ssrdv
end
