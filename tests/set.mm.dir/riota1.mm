include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "wceq.mm"
include "crio.mm"
include "weu.mm"
include "wb.mm"
include "df-reu.mm"
include "iota1.mm"
include "sylbi.mm"
include "df-riota.mm"
include "eqeq1i.mm"
include "syl6bbr.mm"

theorem riota1
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( E! x e. A ph -> ( ( x e. A /\ ph ) <-> ( iota_ x e. A ph ) = x ) )

  proof
    wph
    vx
    cA
    wreu
    #
    vx
    cv
    #
    cA
    wcel
    wph
    wa
    #
    @2
    vx
    cio
    #
    @1
    wceq
    #
    wph
    vx
    cA
    crio
    #
    @1
    wceq
    @0
    @2
    vx
    weu
    @2
    @4
    wb
    wph
    vx
    cA
    df-reu
    @2
    vx
    iota1
    sylbi
    @5
    @3
    @1
    wph
    vx
    cA
    df-riota
    eqeq1i
    syl6bbr
end
