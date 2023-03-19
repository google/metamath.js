include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cme.mm"
include "cmetmet.mm"
include "ax-mp.mm"

theorem cmetmeti
  let cD: class D
  let cX: class X
  let vf: setvar f
  assume cmetmeti.1: |- D e. ( CMet ` X )


  assert |- D e. ( Met ` X )

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
    cmetmeti.1
    cD
    cX
    cmetmet
    ax-mp
end
