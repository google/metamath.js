include "cv.mm"
include "wss.mm"
include "wa.mm"
include "cab.mm"
include "wcel.mm"
include "cint.mm"
include "cvv.mm"
include "wi.mm"
include "wb.mm"
include "a1d.mm"
include "cleq2lem.mm"
include "elab3g.mm"
include "syl.mm"
include "mpbir2and.mm"
include "intss1.mm"

theorem clublem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cX: class X
  let cY: class Y
  assume clublem.y: |- ( ph -> Y e. _V )
  assume clublem.sub: |- ( x = Y -> ( ps <-> ch ) )
  assume clublem.sup: |- ( ph -> X C_ Y )
  assume clublem.maj: |- ( ph -> ch )

  disjoint ch x
  disjoint X x
  disjoint Y x
  assert |- ( ph -> |^| { x | ( X C_ x /\ ps ) } C_ Y )

  proof
    wph
    cY
    cX
    vx
    cv
    #
    wss
    wps
    wa
    #
    vx
    cab
    #
    wcel
    #
    @2
    cint
    cY
    wss
    wph
    @3
    cX
    cY
    wss
    #
    wch
    clublem.sup
    clublem.maj
    wph
    @4
    wch
    wa
    #
    cY
    cvv
    wcel
    #
    wi
    @3
    @5
    wb
    wph
    @6
    @5
    clublem.y
    a1d
    @1
    @5
    vx
    cY
    cvv
    wps
    wch
    @0
    cY
    cX
    clublem.sub
    cleq2lem
    elab3g
    syl
    mpbir2and
    cY
    @2
    intss1
    syl
end
