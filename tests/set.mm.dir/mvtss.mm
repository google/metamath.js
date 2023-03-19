include "cmfs.mm"
include "wcel.mm"
include "cmty.mm"
include "cfv.mm"
include "crn.mm"
include "eqid.mm"
include "mvtval.mm"
include "cmvar.mm"
include "wf.mm"
include "wss.mm"
include "mtyf2.mm"
include "frn.mm"
include "syl.mm"
include "syl5eqss.mm"

theorem mvtss
  let cT: class T
  let cF: class F
  let cK: class K
  assume mvtss.f: |- F = ( mVT ` T )
  assume mvtss.k: |- K = ( mTC ` T )


  assert |- ( T e. mFS -> F C_ K )

  proof
    cT
    cmfs
    wcel
    #
    cF
    cT
    cmty
    cfv
    #
    crn
    #
    cK
    cT
    cF
    @1
    mvtss.f
    @1
    eqid
    #
    mvtval
    @0
    cT
    cmvar
    cfv
    #
    cK
    @1
    wf
    @2
    cK
    wss
    cT
    cK
    @4
    @1
    @4
    eqid
    mvtss.k
    @3
    mtyf2
    @4
    cK
    @1
    frn
    syl
    syl5eqss
end
