include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "cvv.mm"
include "ctrls.mm"
include "df-trls.mm"
include "relmptopab.mm"

theorem reltrls
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p


  assert |- Rel ( Trails ` G )

  proof
    vf
    cv
    #
    vp
    cv
    vg
    cv
    cwlks
    cfv
    wbr
    @0
    ccnv
    wfun
    wa
    vg
    vf
    vp
    cvv
    cG
    ctrls
    vf
    vg
    vp
    df-trls
    relmptopab
end
