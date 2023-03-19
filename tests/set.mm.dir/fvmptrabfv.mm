include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "crab.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "rabeqbidv.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "rabeqdv.mm"
include "rab0.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem fvmptrabfv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cX: class X
  assume fvmptrabfv.f: |- F = ( x e. _V |-> { y e. ( G ` x ) | ph } )
  assume fvmptrabfv.r: |- ( x = X -> ( ph <-> ps ) )

  disjoint G x
  disjoint G y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint ps x
  assert |- ( F ` X ) = { y e. ( G ` X ) | ps }

  proof
    cX
    cvv
    wcel
    #
    cX
    cF
    cfv
    #
    wps
    vy
    cX
    cG
    cfv
    #
    crab
    #
    wceq
    vx
    cX
    wph
    vy
    vx
    cv
    #
    cG
    cfv
    #
    crab
    @3
    cvv
    cF
    @4
    cX
    wceq
    wph
    wps
    vy
    @5
    @2
    @4
    cX
    cG
    fveq2
    fvmptrabfv.r
    rabeqbidv
    fvmptrabfv.f
    wps
    vy
    @2
    cX
    cG
    fvex
    rabex
    fvmpt
    @0
    wn
    #
    @1
    c0
    @3
    cX
    cF
    fvprc
    @6
    @3
    wps
    vy
    c0
    crab
    c0
    @6
    wps
    vy
    @2
    c0
    cX
    cG
    fvprc
    rabeqdv
    wps
    vy
    rab0
    syl6req
    eqtrd
    pm2.61i
end
