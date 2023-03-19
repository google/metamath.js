include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "wral.mm"
include "19.26.mm"
include "df-ral.mm"
include "anbi12i.mm"
include "bitr4i.mm"

theorem r19.26m
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- ( A. x ( ( x e. A -> ph ) /\ ( x e. B -> ps ) ) <-> ( A. x e. A ph /\ A. x e. B ps ) )

  proof
    vx
    cv
    #
    cA
    wcel
    wph
    wi
    #
    @0
    cB
    wcel
    wps
    wi
    #
    wa
    vx
    wal
    @1
    vx
    wal
    #
    @2
    vx
    wal
    #
    wa
    wph
    vx
    cA
    wral
    #
    wps
    vx
    cB
    wral
    #
    wa
    @1
    @2
    vx
    19.26
    @5
    @3
    @6
    @4
    wph
    vx
    cA
    df-ral
    wps
    vx
    cB
    df-ral
    anbi12i
    bitr4i
end
