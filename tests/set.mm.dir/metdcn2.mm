include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "cle.mm"
include "cordt.mm"
include "cr.mm"
include "crest.mm"
include "ccn.mm"
include "cxmt.mm"
include "metxmet.mm"
include "eqid.mm"
include "xmetdcn.mm"
include "syl.mm"
include "cxr.mm"
include "ctopon.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "letopon.mm"
include "a1i.mm"
include "cxp.mm"
include "wf.mm"
include "metf.mm"
include "frn.mm"
include "ressxr.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cioo.mm"
include "ctg.mm"
include "xrtgioo.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"

theorem metdcn2
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
  assume metdcn2.2: |- K = ( topGen ` ran (,) )


  assert |- ( D e. ( Met ` X ) -> D e. ( ( J tX J ) Cn K ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cJ
    cJ
    ctx
    co
    #
    cle
    cordt
    cfv
    #
    cr
    crest
    co
    #
    ccn
    co
    #
    @1
    cK
    ccn
    co
    @0
    cD
    @1
    @2
    ccn
    co
    wcel
    #
    cD
    @4
    wcel
    #
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    @5
    cD
    cX
    metxmet
    cD
    cJ
    @2
    cX
    xmetdcn2.1
    @2
    eqid
    xmetdcn
    syl
    @0
    @2
    cxr
    ctopon
    cfv
    wcel
    #
    cD
    crn
    cr
    wss
    #
    cr
    cxr
    wss
    #
    @5
    @6
    wb
    @7
    @0
    letopon
    a1i
    @0
    cX
    cX
    cxp
    #
    cr
    cD
    wf
    @8
    cD
    cX
    metf
    @10
    cr
    cD
    frn
    syl
    @9
    @0
    ressxr
    a1i
    cr
    cD
    @1
    @2
    cxr
    cnrest2
    syl3anc
    mpbid
    cK
    @3
    @1
    ccn
    cK
    cioo
    crn
    ctg
    cfv
    @3
    metdcn2.2
    @3
    @3
    eqid
    xrtgioo
    eqtri
    oveq2i
    syl6eleqr
end
