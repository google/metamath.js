include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbl.mm"
include "crn.mm"
include "ctg.mm"
include "ctopon.mm"
include "mopnval.mm"
include "cuni.mm"
include "ctb.mm"
include "blbas.mm"
include "tgtopon.mm"
include "syl.mm"
include "unirnbl.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "eqeltrd.mm"

theorem mopntopon
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J e. ( TopOn ` X ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cD
    cbl
    cfv
    crn
    #
    ctg
    cfv
    #
    cX
    ctopon
    cfv
    #
    cD
    cJ
    cX
    mopnval.1
    mopnval
    @0
    @2
    @1
    cuni
    #
    ctopon
    cfv
    #
    @3
    @0
    @1
    ctb
    wcel
    @2
    @5
    wcel
    cD
    cX
    blbas
    @1
    tgtopon
    syl
    @0
    @4
    cX
    ctopon
    cD
    cX
    unirnbl
    fveq2d
    eleqtrd
    eqeltrd
end
