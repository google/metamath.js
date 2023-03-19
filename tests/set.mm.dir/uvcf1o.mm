include "cnzr.mm"
include "wcel.mm"
include "wa.mm"
include "cfrlm.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1.mm"
include "crn.mm"
include "wf1o.mm"
include "eqid.mm"
include "uvcf1.mm"
include "f1f1orn.mm"
include "syl.mm"

theorem uvcf1o
  let cR: class R
  let cU: class U
  let cI: class I
  let cW: class W
  assume uvcf1o.u: |- U = ( R unitVec I )


  assert |- ( ( R e. NzRing /\ I e. W ) -> U : I -1-1-onto-> ran U )

  proof
    cR
    cnzr
    wcel
    cI
    cW
    wcel
    wa
    cI
    cR
    cI
    cfrlm
    co
    #
    cbs
    cfv
    #
    cU
    wf1
    cI
    cU
    crn
    cU
    wf1o
    @1
    cR
    cU
    cI
    cW
    @0
    uvcf1o.u
    @0
    eqid
    @1
    eqid
    uvcf1
    cI
    @1
    cU
    f1f1orn
    syl
end
