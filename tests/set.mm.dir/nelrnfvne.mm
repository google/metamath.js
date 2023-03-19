include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "crn.mm"
include "wnel.mm"
include "wne.mm"
include "fvelrn.mm"
include "elnelne2.mm"
include "stoic3.mm"

theorem nelrnfvne
  let cF: class F
  let cX: class X
  let cY: class Y


  assert |- ( ( Fun F /\ X e. dom F /\ Y e/ ran F ) -> ( F ` X ) =/= Y )

  proof
    cF
    wfun
    cX
    cF
    cdm
    wcel
    cX
    cF
    cfv
    #
    cF
    crn
    #
    wcel
    cY
    @1
    wnel
    @0
    cY
    wne
    cX
    cF
    fvelrn
    @0
    cY
    @1
    elnelne2
    stoic3
end
