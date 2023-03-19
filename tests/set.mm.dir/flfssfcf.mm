include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cflim.mm"
include "cfcls.mm"
include "cflf.mm"
include "cfcf.mm"
include "wss.mm"
include "flimfcls.mm"
include "a1i.mm"
include "flfval.mm"
include "fcfval.mm"
include "3sstr4d.mm"

theorem flfssfcf
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vn: setvar n
  let vo: setvar o
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vs: setvar s
  let vy: setvar y
  let cN: class N
  let cS: class S


  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( ( J fLimf L ) ` F ) C_ ( ( J fClusf L ) ` F ) )

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
    #
    cJ
    cL
    cX
    cF
    cfm
    co
    cfv
    #
    cflim
    co
    #
    cJ
    @1
    cfcls
    co
    #
    cF
    cJ
    cL
    cflf
    co
    cfv
    cF
    cJ
    cL
    cfcf
    co
    cfv
    @2
    @3
    wss
    @0
    @1
    cJ
    flimfcls
    a1i
    cF
    cJ
    cL
    cX
    cY
    flfval
    cF
    cJ
    cL
    cX
    cY
    fcfval
    3sstr4d
end
