include "ctgp.mm"
include "wcel.mm"
include "ctmd.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "tgptmd.mm"
include "tmdcn.mm"
include "syl.mm"

theorem tgpcn
  let cF: class F
  let cG: class G
  let cJ: class J
  assume tgpcn.j: |- J = ( TopOpen ` G )
  assume tgpcn.1: |- F = ( +f ` G )


  assert |- ( G e. TopGrp -> F e. ( ( J tX J ) Cn J ) )

  proof
    cG
    ctgp
    wcel
    cG
    ctmd
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
    cG
    tgptmd
    cF
    cG
    cJ
    tgpcn.j
    tgpcn.1
    tmdcn
    syl
end
