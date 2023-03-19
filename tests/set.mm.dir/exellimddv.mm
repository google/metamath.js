include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "alrimiv.mm"
include "exellim.mm"
include "syl2anc.mm"

theorem exellimddv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume exellimddv.1: |- ( ph -> E. x x e. A )
  assume exellimddv.2: |- ( ph -> ( x e. A -> ps ) )

  disjoint ph x
  disjoint ps x
  assert |- ( ph -> ps )

  proof
    wph
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    @0
    wps
    wi
    #
    vx
    wal
    wps
    exellimddv.1
    wph
    @1
    vx
    exellimddv.2
    alrimiv
    wps
    vx
    cA
    exellim
    syl2anc
end
