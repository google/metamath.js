include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "syl.mm"
include "bj-rabbida2.mm"

theorem bj-rabeqd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume bj-rabeqd.nf: |- F/ x ph
  assume bj-rabeqd.1: |- ( ph -> A = B )


  assert |- ( ph -> { x e. A | ps } = { x e. B | ps } )

  proof
    wph
    wps
    wps
    vx
    cA
    cB
    bj-rabeqd.nf
    wph
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    wcel
    #
    wps
    wa
    @1
    cB
    wcel
    #
    wps
    wa
    wb
    bj-rabeqd.1
    @0
    @2
    @3
    wps
    cA
    cB
    @1
    eleq2
    anbi1d
    syl
    bj-rabbida2
end
