include "cgim.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "eqid.mm"
include "isgim.mm"
include "simplbi.mm"

theorem gimghm
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R GrpIso S ) -> F e. ( R GrpHom S ) )

  proof
    cF
    cR
    cS
    cgim
    co
    wcel
    cF
    cR
    cS
    cghm
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
    isgim
    simplbi
end
