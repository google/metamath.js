include "wral.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "con3.mm"
include "mpi.mm"
include "alimi.mm"
include "df-ral.mm"
include "eq0.mm"
include "3imtr4i.mm"
include "rzal.mm"
include "impbii.mm"

theorem ralf0OLD
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume ralf0.1: |- -. ph

  disjoint A x
  assert |- ( A. x e. A ph <-> A = (/) )

  proof
    wph
    vx
    cA
    wral
    #
    cA
    c0
    wceq
    #
    vx
    cv
    cA
    wcel
    #
    wph
    wi
    #
    vx
    wal
    @2
    wn
    #
    vx
    wal
    @0
    @1
    @3
    @4
    vx
    @3
    wph
    wn
    @4
    ralf0.1
    @2
    wph
    con3
    mpi
    alimi
    wph
    vx
    cA
    df-ral
    vx
    cA
    eq0
    3imtr4i
    wph
    vx
    cA
    rzal
    impbii
end
