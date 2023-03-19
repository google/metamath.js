include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "pm2.21d.mm"
include "ssrdv.mm"
include "ss0.mm"
include "syl.mm"

theorem eq0rdv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume eq0rdv.1: |- ( ph -> -. x e. A )

  disjoint A x
  disjoint ph x
  assert |- ( ph -> A = (/) )

  proof
    wph
    cA
    c0
    wss
    cA
    c0
    wceq
    wph
    vx
    cA
    c0
    wph
    vx
    cv
    #
    cA
    wcel
    @0
    c0
    wcel
    eq0rdv.1
    pm2.21d
    ssrdv
    cA
    ss0
    syl
end
