include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "ctx.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccn.mm"
include "cr.mm"
include "crest.mm"
include "tgioo2.mm"
include "oveq2i.mm"
include "ctop.mm"
include "wss.mm"
include "cnfldtop.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "eqid.mm"
include "metdcn2.mm"
include "sseldi.mm"

theorem metdcn
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
  assume metdcn.2: |- K = ( TopOpen ` CCfld )


  assert |- ( D e. ( Met ` X ) -> D e. ( ( J tX J ) Cn K ) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    cJ
    cJ
    ctx
    co
    #
    cioo
    crn
    ctg
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
    @2
    @0
    cK
    cr
    crest
    co
    #
    ccn
    co
    #
    @3
    @1
    @4
    @0
    ccn
    cK
    metdcn.2
    tgioo2
    oveq2i
    cK
    ctop
    wcel
    @5
    @3
    wss
    cK
    metdcn.2
    cnfldtop
    cr
    @0
    cK
    cnrest2r
    ax-mp
    eqsstri
    cD
    cJ
    @1
    cX
    xmetdcn2.1
    @1
    eqid
    metdcn2
    sseldi
end
