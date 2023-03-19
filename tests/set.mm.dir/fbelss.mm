include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "fbsspw.mm"
include "sselda.mm"
include "elpwid.mm"

theorem fbelss
  let cB: class B
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( fBas ` B ) /\ X e. F ) -> X C_ B )

  proof
    cF
    cB
    cfbas
    cfv
    wcel
    #
    cX
    cF
    wcel
    wa
    cX
    cB
    @0
    cF
    cB
    cpw
    cX
    cB
    cF
    fbsspw
    sselda
    elpwid
end
