include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wral.mm"
include "anclb.mm"
include "albii.mm"
include "df-ral.mm"
include "3bitr4ri.mm"

theorem ralanid
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( A. x e. A ( x e. A /\ ph ) <-> A. x e. A ph )

  proof
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
    @0
    @0
    wph
    wa
    #
    wi
    #
    vx
    wal
    wph
    vx
    cA
    wral
    @2
    vx
    cA
    wral
    @1
    @3
    vx
    @0
    wph
    anclb
    albii
    wph
    vx
    cA
    df-ral
    @2
    vx
    cA
    df-ral
    3bitr4ri
end
