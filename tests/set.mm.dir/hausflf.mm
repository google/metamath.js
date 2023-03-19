include "cha.mm"
include "wcel.mm"
include "cfil.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cflf.mm"
include "co.mm"
include "wmo.mm"
include "cfm.mm"
include "cflim.mm"
include "hausflimi.mm"
include "3ad2ant1.mm"
include "ctopon.mm"
include "wceq.mm"
include "ctop.mm"
include "haustop.mm"
include "toptopon.mm"
include "sylib.mm"
include "flfval.mm"
include "syl3an1.mm"
include "eleq2d.mm"
include "mobidv.mm"
include "mpbird.mm"

theorem hausflf
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  assume hausflf.x: |- X = U. J

  disjoint F x
  disjoint J x
  disjoint L x
  disjoint X x
  disjoint Y x
  assert |- ( ( J e. Haus /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> E* x x e. ( ( J fLimf L ) ` F ) )

  proof
    cJ
    cha
    wcel
    #
    cL
    cY
    cfil
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
    vx
    cv
    #
    cF
    cJ
    cL
    cflf
    co
    cfv
    #
    wcel
    #
    vx
    wmo
    @4
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
    wcel
    #
    vx
    wmo
    #
    @0
    @1
    @10
    @2
    vx
    @7
    cJ
    hausflimi
    3ad2ant1
    @3
    @6
    @9
    vx
    @3
    @5
    @8
    @4
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @1
    @2
    @5
    @8
    wceq
    @0
    cJ
    ctop
    wcel
    @11
    cJ
    haustop
    cJ
    cX
    hausflf.x
    toptopon
    sylib
    cF
    cJ
    cL
    cX
    cY
    flfval
    syl3an1
    eleq2d
    mobidv
    mpbird
end
