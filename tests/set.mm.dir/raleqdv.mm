include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "raleq.mm"
include "syl.mm"

theorem raleqdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleq1d.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( A. x e. A ps <-> A. x e. B ps ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    vx
    cA
    wral
    wps
    vx
    cB
    wral
    wb
    raleq1d.1
    wps
    vx
    cA
    cB
    raleq
    syl
end
