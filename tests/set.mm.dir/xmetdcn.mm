include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "cxrs.mm"
include "cds.mm"
include "cmopn.mm"
include "ccn.mm"
include "cxr.mm"
include "ctopon.mm"
include "wss.mm"
include "cle.mm"
include "cordt.mm"
include "letopon.mm"
include "eqeltri.mm"
include "eqid.mm"
include "xrsmopn.mm"
include "eqsstri.mm"
include "cuni.mm"
include "wceq.mm"
include "xrsxmet.mm"
include "mopnuni.mm"
include "ax-mp.mm"
include "cnss2.mm"
include "mp2an.mm"
include "xmetdcn2.mm"
include "sseldi.mm"

theorem xmetdcn
  let cD: class D
  let cJ: class J
  let cK: class K
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume xmetdcn2.1: |- J = ( MetOpen ` D )
  assume xmetdcn.2: |- K = ( ordTop ` <_ )


  assert |- ( D e. ( *Met ` X ) -> D e. ( ( J tX J ) Cn K ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cJ
    cJ
    ctx
    co
    #
    cxrs
    cds
    cfv
    #
    cmopn
    cfv
    #
    ccn
    co
    #
    @0
    cK
    ccn
    co
    #
    cD
    cK
    cxr
    ctopon
    cfv
    #
    wcel
    cK
    @2
    wss
    @3
    @4
    wss
    cK
    cle
    cordt
    cfv
    #
    @5
    xmetdcn.2
    letopon
    eqeltri
    cK
    @6
    @2
    xmetdcn.2
    @1
    @2
    @1
    eqid
    #
    @2
    eqid
    #
    xrsmopn
    eqsstri
    @0
    @2
    cK
    cxr
    @1
    cxr
    cxmt
    cfv
    wcel
    cxr
    @2
    cuni
    wceq
    @1
    @7
    xrsxmet
    @1
    @2
    cxr
    @8
    mopnuni
    ax-mp
    cnss2
    mp2an
    @1
    cD
    cJ
    @2
    cX
    xmetdcn2.1
    @7
    @8
    xmetdcn2
    sseldi
end
