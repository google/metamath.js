include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "ralimi.mm"

theorem neik0imk0p
  let vx: setvar x
  let cB: class B
  let cN: class N


  assert |- ( A. x e. B B e. ( N ` x ) -> A. x e. B ( N ` x ) =/= (/) )

  proof
    cB
    vx
    cv
    cN
    cfv
    #
    wcel
    @0
    c0
    wne
    vx
    cB
    @0
    cB
    ne0i
    ralimi
end
