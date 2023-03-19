include "cn.mm"
include "wcel.mm"
include "crab.mm"
include "wa.mm"
include "c1.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "1nn.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "elrabi.mm"
include "peano2nn.mm"
include "a1d.mm"
include "anim12d.mm"
include "3imtr4g.mm"
include "mpcom.mm"
include "rgen.mm"
include "peano5nni.mm"
include "mp2an.mm"
include "sseli.mm"
include "sylib.mm"
include "simprd.mm"

theorem nnind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nnind.1: |- ( x = 1 -> ( ph <-> ps ) )
  assume nnind.2: |- ( x = y -> ( ph <-> ch ) )
  assume nnind.3: |- ( x = ( y + 1 ) -> ( ph <-> th ) )
  assume nnind.4: |- ( x = A -> ( ph <-> ta ) )
  assume nnind.5: |- ps
  assume nnind.6: |- ( y e. NN -> ( ch -> th ) )

  disjoint x y
  disjoint A x
  disjoint ps x
  disjoint ch x
  disjoint th x
  disjoint ta x
  disjoint ph y
  assert |- ( A e. NN -> ta )

  proof
    cA
    cn
    wcel
    #
    @0
    wta
    @0
    cA
    wph
    vx
    cn
    crab
    #
    wcel
    @0
    wta
    wa
    cn
    @1
    cA
    c1
    @1
    wcel
    #
    vy
    cv
    #
    c1
    caddc
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    cn
    @1
    wss
    @2
    c1
    cn
    wcel
    wps
    1nn
    nnind.5
    wph
    wps
    vx
    c1
    cn
    nnind.1
    elrab
    mpbir2an
    @5
    vy
    @1
    @3
    cn
    wcel
    #
    @3
    @1
    wcel
    #
    @5
    wph
    vx
    @3
    cn
    elrabi
    @6
    @6
    wch
    wa
    @4
    cn
    wcel
    #
    wth
    wa
    @7
    @5
    @6
    @6
    @8
    wch
    wth
    @6
    @8
    @6
    @3
    peano2nn
    a1d
    nnind.6
    anim12d
    wph
    wch
    vx
    @3
    cn
    nnind.2
    elrab
    wph
    wth
    vx
    @4
    cn
    nnind.3
    elrab
    3imtr4g
    mpcom
    rgen
    vy
    @1
    peano5nni
    mp2an
    sseli
    wph
    wta
    vx
    cA
    cn
    nnind.4
    elrab
    sylib
    simprd
end
