include "cflf.mm"
include "co.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wmo.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cha.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "n0.mm"
include "biimpi.mm"
include "hausflf.mm"
include "wa.mm"
include "weu.mm"
include "euen1b.mm"
include "eu5.mm"
include "bitr2i.mm"
include "syl2anr.mm"

theorem hausflf2
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume hausflf.x: |- X = U. J


  assert |- ( ( ( J e. Haus /\ L e. ( Fil ` Y ) /\ F : Y --> X ) /\ ( ( J fLimf L ) ` F ) =/= (/) ) -> ( ( J fLimf L ) ` F ) ~~ 1o )

  proof
    cF
    cJ
    cL
    cflf
    co
    cfv
    #
    c0
    wne
    #
    vx
    cv
    @0
    wcel
    #
    vx
    wex
    #
    @2
    vx
    wmo
    #
    @0
    c1o
    cen
    wbr
    #
    cJ
    cha
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
    @1
    @3
    vx
    @0
    n0
    biimpi
    vx
    cF
    cJ
    cL
    cX
    cY
    hausflf.x
    hausflf
    @3
    @4
    wa
    #
    @5
    @5
    @2
    vx
    weu
    @6
    vx
    @0
    euen1b
    @2
    vx
    eu5
    bitr2i
    biimpi
    syl2anr
end
