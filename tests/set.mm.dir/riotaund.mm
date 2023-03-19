include "wreu.mm"
include "wn.mm"
include "crio.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "c0.mm"
include "df-riota.mm"
include "weu.mm"
include "wceq.mm"
include "df-reu.mm"
include "iotanul.mm"
include "sylnbi.mm"
include "syl5eq.mm"

theorem riotaund
  let wph: wff ph
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( -. E! x e. A ph -> ( iota_ x e. A ph ) = (/) )

  proof
    wph
    vx
    cA
    wreu
    #
    wn
    wph
    vx
    cA
    crio
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    vx
    cio
    #
    c0
    wph
    vx
    cA
    df-riota
    @0
    @1
    vx
    weu
    @2
    c0
    wceq
    wph
    vx
    cA
    df-reu
    @1
    vx
    iotanul
    sylnbi
    syl5eq
end
