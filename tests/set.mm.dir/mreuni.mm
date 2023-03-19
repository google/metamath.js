include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "mre1cl.mm"
include "mresspw.mm"
include "elpwuni.mm"
include "biimpa.mm"
include "syl2anc.mm"

theorem mreuni
  let cC: class C
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  let cS: class S
  let cI: class I
  let vy: setvar y


  assert |- ( C e. ( Moore ` X ) -> U. C = X )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    cX
    cC
    wcel
    #
    cC
    cX
    cpw
    wss
    #
    cC
    cuni
    cX
    wceq
    #
    cC
    cX
    mre1cl
    cC
    cX
    mresspw
    @0
    @1
    @2
    cC
    cX
    elpwuni
    biimpa
    syl2anc
end
