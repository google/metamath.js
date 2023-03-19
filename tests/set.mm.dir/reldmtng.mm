include "cvv.mm"
include "cv.mm"
include "cnx.mm"
include "cds.mm"
include "cfv.mm"
include "csg.mm"
include "ccom.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cts.mm"
include "cmopn.mm"
include "ctng.mm"
include "df-tng.mm"
include "reldmmpt2.mm"

theorem reldmtng
  let vf: setvar f
  let vg: setvar g
  let cD: class D
  let cG: class G
  let cJ: class J
  let cN: class N


  assert |- Rel dom toNrmGrp

  proof
    vg
    vf
    cvv
    cvv
    vg
    cv
    #
    cnx
    cds
    cfv
    vf
    cv
    @0
    csg
    cfv
    ccom
    #
    cop
    csts
    co
    cnx
    cts
    cfv
    @1
    cmopn
    cfv
    cop
    csts
    co
    ctng
    vf
    vg
    df-tng
    reldmmpt2
end
