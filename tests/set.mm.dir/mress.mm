include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "mresspw.mm"
include "sselda.mm"
include "elpwid.mm"

theorem mress
  let cC: class C
  let cS: class S
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x


  assert |- ( ( C e. ( Moore ` X ) /\ S e. C ) -> S C_ X )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cS
    cC
    wcel
    wa
    cS
    cX
    @0
    cC
    cX
    cpw
    cS
    cC
    cX
    mresspw
    sselda
    elpwid
end
