include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "co.mm"
include "cplusg.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "islss.mm"
include "simp1bi.mm"

theorem lssss
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lssss.v: |- V = ( Base ` W )
  assume lssss.s: |- S = ( LSubSp ` W )


  assert |- ( U e. S -> U C_ V )

  proof
    cU
    cS
    wcel
    cU
    cV
    wss
    cU
    c0
    wne
    vx
    cv
    va
    cv
    cW
    cvsca
    cfv
    #
    co
    vb
    cv
    cW
    cplusg
    cfv
    #
    co
    cU
    wcel
    vb
    cU
    wral
    va
    cU
    wral
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    vx
    @3
    @1
    cS
    @0
    cU
    @2
    cV
    cW
    va
    vb
    @2
    eqid
    @3
    eqid
    lssss.v
    @1
    eqid
    @0
    eqid
    lssss.s
    islss
    simp1bi
end
