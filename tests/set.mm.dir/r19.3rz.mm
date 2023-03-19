include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "n0.mm"
include "biimt.mm"
include "sylbi.mm"
include "wal.mm"
include "df-ral.mm"
include "19.23.mm"
include "bitri.mm"
include "syl6bbr.mm"

theorem r19.3rz
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume r19.3rz.1: |- F/ x ph

  disjoint A x
  assert |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) )

  proof
    cA
    c0
    wne
    #
    wph
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    #
    wph
    wi
    #
    wph
    vx
    cA
    wral
    #
    @0
    @2
    wph
    @3
    wb
    vx
    cA
    n0
    @2
    wph
    biimt
    sylbi
    @4
    @1
    wph
    wi
    vx
    wal
    @3
    wph
    vx
    cA
    df-ral
    @1
    wph
    vx
    r19.3rz.1
    19.23
    bitri
    syl6bbr
end
