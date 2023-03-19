include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "weu.mm"
include "wmo.mm"
include "wi.mm"
include "2euswap.mm"
include "moani.mm"
include "ancom.mm"
include "mobii.mm"
include "mpbi.mm"
include "mpg.mm"
include "moeq.mm"
include "impbii.mm"
include "biidd.mm"
include "ceqsexv.mm"
include "eubii.mm"
include "bitri.mm"

theorem euxfr2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume euxfr2.1: |- A e. _V
  assume euxfr2.2: |- E* y x = A

  disjoint ph x
  disjoint A x
  assert |- ( E! x E. y ( x = A /\ ph ) <-> E! y ph )

  proof
    vx
    cv
    cA
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    weu
    #
    @1
    vx
    wex
    #
    vy
    weu
    #
    wph
    vy
    weu
    @2
    @4
    @1
    vy
    wmo
    #
    @2
    @4
    wi
    vx
    @1
    vx
    vy
    2euswap
    wph
    @0
    wa
    #
    vy
    wmo
    @5
    @0
    wph
    vy
    euxfr2.2
    moani
    @6
    @1
    vy
    wph
    @0
    ancom
    #
    mobii
    mpbi
    mpg
    @1
    vx
    wmo
    #
    @4
    @2
    wi
    vy
    @1
    vy
    vx
    2euswap
    @6
    vx
    wmo
    @8
    @0
    wph
    vx
    vx
    cA
    moeq
    moani
    @6
    @1
    vx
    @7
    mobii
    mpbi
    mpg
    impbii
    @3
    wph
    vy
    wph
    wph
    vx
    cA
    euxfr2.1
    @0
    wph
    biidd
    ceqsexv
    eubii
    bitri
end
