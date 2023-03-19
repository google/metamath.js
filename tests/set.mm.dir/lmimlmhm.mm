include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "clmhm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "eqid.mm"
include "islmim.mm"
include "simplbi.mm"

theorem lmimlmhm
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R LMIso S ) -> F e. ( R LMHom S ) )

  proof
    cF
    cR
    cS
    clmim
    co
    wcel
    cF
    cR
    cS
    clmhm
    co
    wcel
    cR
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cF
    wf1o
    @0
    @1
    cR
    cS
    cF
    @0
    eqid
    @1
    eqid
    islmim
    simplbi
end
