include "wral.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "exintr.mm"
include "sylbi.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "impcom.mm"

theorem r19.2z
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A =/= (/) /\ A. x e. A ph ) -> E. x e. A ph )

  proof
    wph
    vx
    cA
    wral
    #
    cA
    c0
    wne
    #
    wph
    vx
    cA
    wrex
    #
    @0
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    #
    @3
    wph
    wa
    vx
    wex
    #
    @1
    @2
    @0
    @3
    wph
    wi
    vx
    wal
    @4
    @5
    wi
    wph
    vx
    cA
    df-ral
    @3
    wph
    vx
    exintr
    sylbi
    vx
    cA
    n0
    wph
    vx
    cA
    df-rex
    3imtr4g
    impcom
end
