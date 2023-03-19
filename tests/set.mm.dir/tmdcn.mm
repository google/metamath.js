include "ctmd.mm"
include "wcel.mm"
include "cmnd.mm"
include "ctps.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "istmd.mm"
include "simp3bi.mm"

theorem tmdcn
  let cF: class F
  let cG: class G
  let cJ: class J
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume tgpcn.1: |- F = ( +f ` G )


  assert |- ( G e. TopMnd -> F e. ( ( J tX J ) Cn J ) )

  proof
    cG
    ctmd
    wcel
    cG
    cmnd
    wcel
    cG
    ctps
    wcel
    cF
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    cF
    cG
    cJ
    tgpcn.1
    tgpcn.j
    istmd
    simp3bi
end
