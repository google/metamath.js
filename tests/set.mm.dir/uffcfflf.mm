include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cufil.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "cfcls.mm"
include "cflim.mm"
include "cfcf.mm"
include "cflf.mm"
include "wceq.mm"
include "toponmax.mm"
include "fmufil.mm"
include "syl3an1.mm"
include "uffclsflim.mm"
include "syl.mm"
include "cfil.mm"
include "ufilfil.mm"
include "fcfval.mm"
include "syl3an2.mm"
include "flfval.mm"
include "3eqtr4d.mm"

theorem uffcfflf
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


  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( UFil ` Y ) /\ F : Y --> X ) -> ( ( J fClusf L ) ` F ) = ( ( J fLimf L ) ` F ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cufil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
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
    cfcls
    co
    #
    cJ
    @4
    cflim
    co
    #
    cF
    cJ
    cL
    cfcf
    co
    cfv
    #
    cF
    cJ
    cL
    cflf
    co
    cfv
    #
    @3
    @4
    cX
    cufil
    cfv
    wcel
    #
    @5
    @6
    wceq
    @0
    cX
    cJ
    wcel
    @1
    @2
    @9
    cX
    cJ
    toponmax
    cJ
    cF
    cL
    cX
    cY
    fmufil
    syl3an1
    @4
    cJ
    cX
    uffclsflim
    syl
    @1
    @0
    cL
    cY
    cfil
    cfv
    wcel
    #
    @2
    @7
    @5
    wceq
    cL
    cY
    ufilfil
    #
    cF
    cJ
    cL
    cX
    cY
    fcfval
    syl3an2
    @1
    @0
    @10
    @2
    @8
    @6
    wceq
    @11
    cF
    cJ
    cL
    cX
    cY
    flfval
    syl3an2
    3eqtr4d
end
