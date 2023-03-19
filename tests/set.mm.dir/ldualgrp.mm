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
include "ldualgrplem.mm"

theorem ldualgrp
  let wph: wff ph
  let cD: class D
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cR: class R
  let cV: class V
  assume ldualgrp.d: |- D = ( LDual ` W )
  assume ldualgrp.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> D e. Grp )

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
    ldualgrp.d
    ldualgrp.w
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
    ldualgrplem
end
