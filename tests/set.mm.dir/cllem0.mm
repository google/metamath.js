include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "wi.mm"
include "wal.mm"
include "elexi.mm"
include "elab2.mm"
include "ralbii.mm"
include "df-ral.mm"
include "3bitri.mm"
include "vex.mm"
include "syl2anb.mm"
include "ex.mm"
include "alrimiv.mm"
include "mpgbir.mm"

theorem cllem0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cU: class U
  let cV: class V
  assume cllem0.v: |- V = { z | ph }
  assume cllem0.rex: |- R e. U
  assume cllem0.r: |- ( z = R -> ( ph <-> ps ) )
  assume cllem0.x: |- ( z = x -> ( ph <-> ch ) )
  assume cllem0.y: |- ( z = y -> ( ph <-> th ) )
  assume cllem0.closed: |- ( ( ch /\ th ) -> ps )

  disjoint ps z
  disjoint ch z
  disjoint th z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint V y
  disjoint R z
  assert |- A. x e. V A. y e. V R e. V

  proof
    cR
    cV
    wcel
    #
    vy
    cV
    wral
    #
    vx
    cV
    wral
    #
    vx
    cv
    #
    cV
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    wps
    wi
    #
    vy
    wal
    #
    wi
    #
    vx
    @2
    wps
    vy
    cV
    wral
    #
    vx
    cV
    wral
    @8
    vx
    cV
    wral
    @9
    vx
    wal
    @1
    @10
    vx
    cV
    @0
    wps
    vy
    cV
    wph
    wps
    vz
    cR
    cV
    cR
    cU
    cllem0.rex
    elexi
    cllem0.r
    cllem0.v
    elab2
    ralbii
    ralbii
    @10
    @8
    vx
    cV
    wps
    vy
    cV
    df-ral
    ralbii
    @8
    vx
    cV
    df-ral
    3bitri
    @4
    @7
    vy
    @4
    @6
    wps
    @4
    wch
    wth
    wps
    @6
    wph
    wch
    vz
    @3
    cV
    vx
    vex
    cllem0.x
    cllem0.v
    elab2
    wph
    wth
    vz
    @5
    cV
    vy
    vex
    cllem0.y
    cllem0.v
    elab2
    cllem0.closed
    syl2anb
    ex
    alrimiv
    mpgbir
end
