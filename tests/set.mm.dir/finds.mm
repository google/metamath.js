include "com.mm"
include "wcel.mm"
include "cab.mm"
include "c0.mm"
include "cv.mm"
include "csuc.mm"
include "wi.mm"
include "wral.mm"
include "wss.mm"
include "0ex.mm"
include "elab.mm"
include "mpbir.mm"
include "vex.mm"
include "sucex.mm"
include "3imtr4g.mm"
include "rgen.mm"
include "peano5.mm"
include "mp2an.mm"
include "sseli.mm"
include "elabg.mm"
include "mpbid.mm"

theorem finds
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume finds.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume finds.2: |- ( x = y -> ( ph <-> ch ) )
  assume finds.3: |- ( x = suc y -> ( ph <-> th ) )
  assume finds.4: |- ( x = A -> ( ph <-> ta ) )
  assume finds.5: |- ps
  assume finds.6: |- ( y e. _om -> ( ch -> th ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( A e. _om -> ta )

  proof
    cA
    com
    wcel
    cA
    wph
    vx
    cab
    #
    wcel
    wta
    com
    @0
    cA
    c0
    @0
    wcel
    #
    vy
    cv
    #
    @0
    wcel
    #
    @2
    csuc
    #
    @0
    wcel
    #
    wi
    #
    vy
    com
    wral
    com
    @0
    wss
    @1
    wps
    finds.5
    wph
    wps
    vx
    c0
    0ex
    finds.1
    elab
    mpbir
    @6
    vy
    com
    @2
    com
    wcel
    wch
    wth
    @3
    @5
    finds.6
    wph
    wch
    vx
    @2
    vy
    vex
    #
    finds.2
    elab
    wph
    wth
    vx
    @4
    @2
    @7
    sucex
    finds.3
    elab
    3imtr4g
    rgen
    vy
    @0
    peano5
    mp2an
    sseli
    wph
    wta
    vx
    cA
    com
    finds.4
    elabg
    mpbid
end
