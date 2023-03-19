include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cgim.mm"
include "clmhm.mm"
include "lmimlmhm.mm"
include "lmghm.mm"
include "syl.mm"
include "eqid.mm"
include "lmimf1o.mm"
include "isgim.mm"
include "sylanbrc.mm"

theorem lmimgim
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R LMIso S ) -> F e. ( R GrpIso S ) )

  proof
    cF
    cR
    cS
    clmim
    co
    wcel
    #
    cF
    cR
    cS
    cghm
    co
    wcel
    #
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
    cF
    cR
    cS
    cgim
    co
    wcel
    @0
    cF
    cR
    cS
    clmhm
    co
    wcel
    @1
    cR
    cS
    cF
    lmimlmhm
    cR
    cS
    cF
    lmghm
    syl
    @2
    @3
    cR
    cS
    cF
    @2
    eqid
    #
    @3
    eqid
    #
    lmimf1o
    @2
    @3
    cR
    cS
    cF
    @4
    @5
    isgim
    sylanbrc
end
