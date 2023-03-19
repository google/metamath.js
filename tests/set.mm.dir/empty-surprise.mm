include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "alimp-surprise.mm"
include "simpli.mm"
include "df-ral.mm"
include "mpbir.mm"

theorem empty-surprise
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vk: setvar k
  assume empty-surprise.1: |- -. E. x x e. A


  assert |- A. x e. A ph

  proof
    wph
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    #
    wph
    wi
    vx
    wal
    #
    @1
    @0
    wph
    wn
    wi
    vx
    wal
    @0
    wph
    vx
    empty-surprise.1
    alimp-surprise
    simpli
    wph
    vx
    cA
    df-ral
    mpbir
end
