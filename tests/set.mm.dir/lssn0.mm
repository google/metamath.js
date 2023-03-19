include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "wral.mm"
include "csca.mm"
include "eqid.mm"
include "islss.mm"
include "simp2bi.mm"

theorem lssn0
  let cS: class S
  let cU: class U
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  assume lssn0.s: |- S = ( LSubSp ` W )


  assert |- ( U e. S -> U =/= (/) )

  proof
    cU
    cS
    wcel
    cU
    cW
    cbs
    cfv
    #
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
    @4
    @2
    cS
    @1
    cU
    @3
    @0
    cW
    va
    vb
    @3
    eqid
    @4
    eqid
    @0
    eqid
    @2
    eqid
    @1
    eqid
    lssn0.s
    islss
    simp2bi
end
