include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "df-ral.mm"
include "impexp.mm"
include "albii.mm"
include "imbi2i.mm"
include "3bitr4i.mm"
include "bitr4i.mm"

theorem r2allem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume r2allem.1: |- ( A. y ( x e. A -> ( y e. B -> ph ) ) <-> ( x e. A -> A. y ( y e. B -> ph ) ) )


  assert |- ( A. x e. A A. y e. B ph <-> A. x A. y ( ( x e. A /\ y e. B ) -> ph ) )

  proof
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wral
    vx
    cv
    cA
    wcel
    #
    @0
    wi
    #
    vx
    wal
    @1
    vy
    cv
    cB
    wcel
    #
    wa
    wph
    wi
    #
    vy
    wal
    #
    vx
    wal
    @0
    vx
    cA
    df-ral
    @5
    @2
    vx
    @1
    @3
    wph
    wi
    #
    wi
    #
    vy
    wal
    @1
    @6
    vy
    wal
    #
    wi
    @5
    @2
    r2allem.1
    @4
    @7
    vy
    @1
    @3
    wph
    impexp
    albii
    @0
    @8
    @1
    wph
    vy
    cB
    df-ral
    imbi2i
    3bitr4i
    albii
    bitr4i
end
