include "cv.mm"
include "ctrls.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "ciedg.mm"
include "cdm.mm"
include "wfo.mm"
include "wa.mm"
include "cvv.mm"
include "ceupth.mm"
include "df-eupth.mm"
include "relmptopab.mm"

theorem releupth
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p


  assert |- Rel ( EulerPaths ` G )

  proof
    vf
    cv
    #
    vp
    cv
    vg
    cv
    #
    ctrls
    cfv
    wbr
    cc0
    @0
    chash
    cfv
    cfzo
    co
    @1
    ciedg
    cfv
    cdm
    @0
    wfo
    wa
    vg
    vf
    vp
    cvv
    cG
    ceupth
    vf
    vg
    vp
    df-eupth
    relmptopab
end
