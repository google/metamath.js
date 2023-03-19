include "cmsr.mm"
include "cfv.mm"
include "crn.mm"
include "eqid.mm"
include "mstaval.mm"
include "wf.mm"
include "wss.mm"
include "msrf.mm"
include "frn.mm"
include "ax-mp.mm"
include "eqsstri.mm"

theorem mstapst
  let cP: class P
  let cS: class S
  let cT: class T
  assume mstapst.p: |- P = ( mPreSt ` T )
  assume mstapst.s: |- S = ( mStat ` T )


  assert |- S C_ P

  proof
    cS
    cT
    cmsr
    cfv
    #
    crn
    #
    cP
    @0
    cS
    cT
    @0
    eqid
    #
    mstapst.s
    mstaval
    cP
    cP
    @0
    wf
    @1
    cP
    wss
    cP
    @0
    cT
    mstapst.p
    @2
    msrf
    cP
    cP
    @0
    frn
    ax-mp
    eqsstri
end
