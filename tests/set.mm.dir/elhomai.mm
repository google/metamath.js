include "cop.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wcel.mm"
include "eqidd.mm"
include "elhoma.mm"
include "mpbir2and.mm"

theorem elhomai
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vz: setvar z
  assume homarcl.h: |- H = ( HomA ` C )
  assume homafval.b: |- B = ( Base ` C )
  assume homafval.c: |- ( ph -> C e. Cat )
  assume homaval.j: |- J = ( Hom ` C )
  assume homaval.x: |- ( ph -> X e. B )
  assume homaval.y: |- ( ph -> Y e. B )
  assume elhomai.f: |- ( ph -> F e. ( X J Y ) )


  assert |- ( ph -> <. X , Y >. ( X H Y ) F )

  proof
    wph
    cX
    cY
    cop
    #
    cF
    cX
    cY
    cH
    co
    wbr
    @0
    @0
    wceq
    cF
    cX
    cY
    cJ
    co
    wcel
    wph
    @0
    eqidd
    elhomai.f
    wph
    cB
    cC
    cF
    cH
    cJ
    cX
    cY
    @0
    homarcl.h
    homafval.b
    homafval.c
    homaval.j
    homaval.x
    homaval.y
    elhoma
    mpbir2and
end
