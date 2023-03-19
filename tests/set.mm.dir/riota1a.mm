include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wreu.mm"
include "cio.mm"
include "wceq.mm"
include "ibar.mm"
include "weu.mm"
include "wb.mm"
include "df-reu.mm"
include "iota1.mm"
include "sylbi.mm"
include "sylan9bb.mm"

theorem riota1a
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( ( x e. A /\ E! x e. A ph ) -> ( ph <-> ( iota x ( x e. A /\ ph ) ) = x ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    wph
    @1
    wph
    wa
    #
    wph
    vx
    cA
    wreu
    #
    @2
    vx
    cio
    @0
    wceq
    #
    @1
    wph
    ibar
    @3
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
    sylan9bb
end
