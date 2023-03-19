include "ctrg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ctmd.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "eqid.mm"
include "trgtmd.mm"
include "mgptopn.mm"
include "tmdcn.mm"
include "syl.mm"

theorem mulrcn
  let cR: class R
  let cT: class T
  let cJ: class J
  assume mulrcn.j: |- J = ( TopOpen ` R )
  assume mulrcn.t: |- T = ( +f ` ( mulGrp ` R ) )


  assert |- ( R e. TopRing -> T e. ( ( J tX J ) Cn J ) )

  proof
    cR
    ctrg
    wcel
    cR
    cmgp
    cfv
    #
    ctmd
    wcel
    cT
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    cR
    @0
    @0
    eqid
    #
    trgtmd
    cT
    @0
    cJ
    cR
    cJ
    @0
    @1
    mulrcn.j
    mgptopn
    mulrcn.t
    tmdcn
    syl
end
