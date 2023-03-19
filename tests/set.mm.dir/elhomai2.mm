include "cotp.mm"
include "cop.mm"
include "co.mm"
include "df-ot.mm"
include "wbr.mm"
include "wcel.mm"
include "elhomai.mm"
include "df-br.mm"
include "sylib.mm"
include "syl5eqel.mm"

theorem elhomai2
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


  assert |- ( ph -> <. X , Y , F >. e. ( X H Y ) )

  proof
    wph
    cX
    cY
    cF
    cotp
    cX
    cY
    cop
    #
    cF
    cop
    #
    cX
    cY
    cH
    co
    #
    cX
    cY
    cF
    df-ot
    wph
    @0
    cF
    @2
    wbr
    @1
    @2
    wcel
    wph
    cB
    cC
    cF
    cH
    cJ
    cX
    cY
    homarcl.h
    homafval.b
    homafval.c
    homaval.j
    homaval.x
    homaval.y
    elhomai.f
    elhomai
    @0
    cF
    @2
    df-br
    sylib
    syl5eqel
end
