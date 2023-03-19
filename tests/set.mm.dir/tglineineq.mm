include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wmo.mm"
include "wceq.mm"
include "tglineintmo.mm"
include "elin.mm"
include "sylib.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "moi.mm"
include "syl212anc.mm"

theorem tglineineq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume tglineintmo.p: |- P = ( Base ` G )
  assume tglineintmo.i: |- I = ( Itv ` G )
  assume tglineintmo.l: |- L = ( LineG ` G )
  assume tglineintmo.g: |- ( ph -> G e. TarskiG )
  assume tglineintmo.a: |- ( ph -> A e. ran L )
  assume tglineintmo.b: |- ( ph -> B e. ran L )
  assume tglineintmo.c: |- ( ph -> A =/= B )
  assume tglineineq.x: |- ( ph -> X e. ( A i^i B ) )
  assume tglineineq.y: |- ( ph -> Y e. ( A i^i B ) )


  assert |- ( ph -> X = Y )

  proof
    wph
    cX
    cA
    cB
    cin
    #
    wcel
    #
    cY
    @0
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    @3
    cB
    wcel
    #
    wa
    #
    vx
    wmo
    cX
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cY
    cA
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    wceq
    tglineineq.x
    tglineineq.y
    wph
    vx
    cA
    cB
    cP
    cG
    cI
    cL
    tglineintmo.p
    tglineintmo.i
    tglineintmo.l
    tglineintmo.g
    tglineintmo.a
    tglineintmo.b
    tglineintmo.c
    tglineintmo
    wph
    @1
    @9
    tglineineq.x
    cX
    cA
    cB
    elin
    sylib
    wph
    @2
    @12
    tglineineq.y
    cY
    cA
    cB
    elin
    sylib
    @6
    @9
    @12
    vx
    cX
    cY
    @0
    @0
    @3
    cX
    wceq
    @4
    @7
    @5
    @8
    @3
    cX
    cA
    eleq1
    @3
    cX
    cB
    eleq1
    anbi12d
    @3
    cY
    wceq
    @4
    @10
    @5
    @11
    @3
    cY
    cA
    eleq1
    @3
    cY
    cB
    eleq1
    anbi12d
    moi
    syl212anc
end
