include "crs.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cgim.mm"
include "crh.mm"
include "eqid.mm"
include "rimrhm.mm"
include "rhmghm.mm"
include "syl.mm"
include "rimf1o.mm"
include "isgim.mm"
include "sylanbrc.mm"

theorem rimgim
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R RingIso S ) -> F e. ( R GrpIso S ) )

  proof
    cF
    cR
    cS
    crs
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
    crh
    co
    wcel
    @1
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
    rimrhm
    cR
    cS
    cF
    rhmghm
    syl
    @2
    @3
    cR
    cS
    cF
    @4
    @5
    rimf1o
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
