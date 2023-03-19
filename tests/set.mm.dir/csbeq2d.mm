include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "csb.mm"
include "eleq2d.mm"
include "sbcbid.mm"
include "abbidv.mm"
include "df-csb.mm"
include "3eqtr4g.mm"

theorem csbeq2d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume csbeq2d.1: |- F/ x ph
  assume csbeq2d.2: |- ( ph -> B = C )


  assert |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C )

  proof
    wph
    vy
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    @0
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    vx
    cA
    cB
    csb
    vx
    cA
    cC
    csb
    wph
    @2
    @4
    vy
    wph
    @1
    @3
    vx
    cA
    csbeq2d.1
    wph
    cB
    cC
    @0
    csbeq2d.2
    eleq2d
    sbcbid
    abbidv
    vx
    vy
    cA
    cB
    df-csb
    vx
    vy
    cA
    cC
    df-csb
    3eqtr4g
end
