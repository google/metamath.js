include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cnrm.mm"
include "ct1.mm"
include "creg.mm"
include "metnrm.mm"
include "cha.mm"
include "methaus.mm"
include "haust1.mm"
include "syl.mm"
include "nrmreg.mm"
include "syl2anc.mm"

theorem metreg
  let cD: class D
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume metnrm.j: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J e. Reg )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cnrm
    wcel
    cJ
    ct1
    wcel
    #
    cJ
    creg
    wcel
    cD
    cJ
    cX
    metnrm.j
    metnrm
    @0
    cJ
    cha
    wcel
    @1
    cD
    cJ
    cX
    metnrm.j
    methaus
    cJ
    haust1
    syl
    cJ
    nrmreg
    syl2anc
end
