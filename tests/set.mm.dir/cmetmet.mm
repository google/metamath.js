include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cmopn.mm"
include "cv.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "ccfil.mm"
include "wral.mm"
include "eqid.mm"
include "iscmet.mm"
include "simplbi.mm"

theorem cmetmet
  let cD: class D
  let cX: class X
  let vf: setvar f


  assert |- ( D e. ( CMet ` X ) -> D e. ( Met ` X ) )

  proof
    cD
    cX
    cms
    cfv
    wcel
    cD
    cX
    cme
    cfv
    wcel
    cD
    cmopn
    cfv
    #
    vf
    cv
    cflim
    co
    c0
    wne
    vf
    cD
    ccfil
    cfv
    wral
    cD
    vf
    @0
    cX
    @0
    eqid
    iscmet
    simplbi
end
