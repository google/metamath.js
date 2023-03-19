include "cv.mm"
include "com.mm"
include "wcel.mm"
include "wi.mm"
include "cab.mm"
include "c0.mm"
include "csuc.mm"
include "wral.mm"
include "wss.mm"
include "0ex.mm"
include "wceq.mm"
include "imbi2d.mm"
include "elab.mm"
include "mpbir.mm"
include "a2d.mm"
include "vex.mm"
include "sucex.mm"
include "3imtr4g.mm"
include "rgen.mm"
include "peano5.mm"
include "mp2an.mm"
include "sseli.mm"
include "abid.mm"
include "sylib.mm"

theorem finds2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  assume finds2.1: |- ( x = (/) -> ( ph <-> ps ) )
  assume finds2.2: |- ( x = y -> ( ph <-> ch ) )
  assume finds2.3: |- ( x = suc y -> ( ph <-> th ) )
  assume finds2.4: |- ( ta -> ps )
  assume finds2.5: |- ( y e. _om -> ( ta -> ( ch -> th ) ) )

  disjoint x y
  disjoint ta x
  disjoint ta y
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ph y
  assert |- ( x e. _om -> ( ta -> ph ) )

  proof
    vx
    cv
    #
    com
    wcel
    @0
    wta
    wph
    wi
    #
    vx
    cab
    #
    wcel
    @1
    com
    @2
    @0
    c0
    @2
    wcel
    #
    vy
    cv
    #
    @2
    wcel
    #
    @4
    csuc
    #
    @2
    wcel
    #
    wi
    #
    vy
    com
    wral
    com
    @2
    wss
    @3
    wta
    wps
    wi
    #
    finds2.4
    @1
    @9
    vx
    c0
    0ex
    @0
    c0
    wceq
    wph
    wps
    wta
    finds2.1
    imbi2d
    elab
    mpbir
    @8
    vy
    com
    @4
    com
    wcel
    #
    wta
    wch
    wi
    #
    wta
    wth
    wi
    #
    @5
    @7
    @10
    wta
    wch
    wth
    finds2.5
    a2d
    @1
    @11
    vx
    @4
    vy
    vex
    #
    @0
    @4
    wceq
    wph
    wch
    wta
    finds2.2
    imbi2d
    elab
    @1
    @12
    vx
    @6
    @4
    @13
    sucex
    @0
    @6
    wceq
    wph
    wth
    wta
    finds2.3
    imbi2d
    elab
    3imtr4g
    rgen
    vy
    @2
    peano5
    mp2an
    sseli
    @1
    vx
    abid
    sylib
end
