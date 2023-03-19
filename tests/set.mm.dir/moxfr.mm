include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wmo.mm"
include "cvv.mm"
include "wrex.mm"
include "wcel.mm"
include "cv.mm"
include "a1i.mm"
include "wceq.mm"
include "euex.mm"
include "ax-mp.mm"
include "rexv.mm"
include "mpbir.mm"
include "rexxfr.mm"
include "3bitr3i.mm"
include "euxfr.mm"
include "imbi12i.mm"
include "df-mo.mm"
include "3bitr4i.mm"

theorem moxfr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume moxfr.a: |- A e. _V
  assume moxfr.b: |- E! y x = A
  assume moxfr.c: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint ph y
  disjoint A x
  disjoint x y
  assert |- ( E* x ph <-> E* y ps )

  proof
    wph
    vx
    wex
    #
    wph
    vx
    weu
    #
    wi
    wps
    vy
    wex
    #
    wps
    vy
    weu
    #
    wi
    wph
    vx
    wmo
    wps
    vy
    wmo
    @0
    @2
    @1
    @3
    wph
    vx
    cvv
    wrex
    wps
    vy
    cvv
    wrex
    @0
    @2
    wph
    wps
    vx
    vy
    cA
    cvv
    cvv
    cA
    cvv
    wcel
    vy
    cv
    cvv
    wcel
    moxfr.a
    a1i
    vx
    cv
    #
    cA
    wceq
    #
    vy
    cvv
    wrex
    #
    @4
    cvv
    wcel
    @6
    @5
    vy
    wex
    #
    @5
    vy
    weu
    @7
    moxfr.b
    @5
    vy
    euex
    ax-mp
    @5
    vy
    rexv
    mpbir
    a1i
    moxfr.c
    rexxfr
    wph
    vx
    rexv
    wps
    vy
    rexv
    3bitr3i
    wph
    wps
    vx
    vy
    cA
    moxfr.a
    moxfr.b
    moxfr.c
    euxfr
    imbi12i
    wph
    vx
    df-mo
    wps
    vy
    df-mo
    3bitr4i
end
