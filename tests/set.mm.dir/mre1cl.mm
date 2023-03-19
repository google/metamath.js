include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "wi.mm"
include "wral.mm"
include "ismre.mm"
include "simp2bi.mm"

theorem mre1cl
  let cC: class C
  let cX: class X
  let vc: setvar c
  let vs: setvar s
  let vx: setvar x
  let cS: class S


  assert |- ( C e. ( Moore ` X ) -> X e. C )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    cC
    cX
    cpw
    wss
    cX
    cC
    wcel
    vs
    cv
    #
    c0
    wne
    @0
    cint
    cC
    wcel
    wi
    vs
    cC
    cpw
    wral
    cC
    cX
    vs
    ismre
    simp2bi
end
