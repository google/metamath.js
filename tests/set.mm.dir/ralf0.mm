include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "mtt.mm"
include "ax-mp.mm"
include "albii.mm"
include "eq0.mm"
include "df-ral.mm"
include "3bitr4ri.mm"

theorem ralf0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume ralf0.1: |- -. ph

  disjoint A x
  assert |- ( A. x e. A ph <-> A = (/) )

  proof
    vx
    cv
    cA
    wcel
    #
    wn
    #
    vx
    wal
    @0
    wph
    wi
    #
    vx
    wal
    cA
    c0
    wceq
    wph
    vx
    cA
    wral
    @1
    @2
    vx
    wph
    wn
    @1
    @2
    wb
    ralf0.1
    wph
    @0
    mtt
    ax-mp
    albii
    vx
    cA
    eq0
    wph
    vx
    cA
    df-ral
    3bitr4ri
end
