include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "wfo.mm"
include "crn.mm"
include "wceq.mm"
include "pjhfo.mm"
include "forn.mm"
include "syl.mm"

theorem pjrn
  let cH: class H


  assert |- ( H e. CH -> ran ( projh ` H ) = H )

  proof
    cH
    cch
    wcel
    chil
    cH
    cH
    cpjh
    cfv
    #
    wfo
    @0
    crn
    cH
    wceq
    cH
    pjhfo
    chil
    cH
    @0
    forn
    syl
end
