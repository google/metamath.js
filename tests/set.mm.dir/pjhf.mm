include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "wfo.mm"
include "wf.mm"
include "pjhfo.mm"
include "fof.mm"
include "syl.mm"
include "chss.mm"
include "fssd.mm"

theorem pjhf
  let cH: class H


  assert |- ( H e. CH -> ( projh ` H ) : ~H --> ~H )

  proof
    cH
    cch
    wcel
    #
    chil
    cH
    chil
    cH
    cpjh
    cfv
    #
    @0
    chil
    cH
    @1
    wfo
    chil
    cH
    @1
    wf
    cH
    pjhfo
    chil
    cH
    @1
    fof
    syl
    cH
    chss
    fssd
end
