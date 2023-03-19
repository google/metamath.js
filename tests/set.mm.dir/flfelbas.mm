include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cflf.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "isflf.mm"
include "simprbda.mm"

theorem flfelbas
  let cA: class A
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vo: setvar o
  let vs: setvar s


  assert |- ( ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) /\ A e. ( ( J fLimf L ) ` F ) ) -> A e. X )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    cL
    cY
    cfil
    cfv
    wcel
    cY
    cX
    cF
    wf
    w3a
    cA
    cF
    cJ
    cL
    cflf
    co
    cfv
    wcel
    cA
    cX
    wcel
    cA
    vo
    cv
    #
    wcel
    cF
    vs
    cv
    cima
    @0
    wss
    vs
    cL
    wrex
    wi
    vo
    cJ
    wral
    cA
    vo
    cF
    cJ
    cL
    cX
    cY
    vs
    isflf
    simprbda
end
