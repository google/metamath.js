include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "csca.mm"
include "cvsca.mm"
include "cmulr.mm"
include "clfn.mm"
include "cbs.mm"
include "coppr.mm"
include "eqid.mm"
include "lduallmodlem.mm"

theorem lduallmod
  let wph: wff ph
  let cD: class D
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cK: class K
  let cR: class R
  let c.x: class .x.
  assume lduallmod.d: |- D = ( LDual ` W )
  assume lduallmod.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> D e. LMod )

  proof
    wph
    cD
    cW
    cplusg
    cfv
    cof
    #
    cW
    csca
    cfv
    #
    cD
    cvsca
    cfv
    #
    @1
    cmulr
    cfv
    #
    cW
    clfn
    cfv
    #
    @1
    cbs
    cfv
    #
    @1
    coppr
    cfv
    #
    cW
    cbs
    cfv
    #
    cW
    lduallmod.d
    lduallmod.w
    @7
    eqid
    @0
    eqid
    @4
    eqid
    @1
    eqid
    @5
    eqid
    @3
    eqid
    @6
    eqid
    @2
    eqid
    lduallmodlem
end
