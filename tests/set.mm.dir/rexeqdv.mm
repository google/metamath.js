include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "rexeq.mm"
include "syl.mm"

theorem rexeqdv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleq1d.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( E. x e. A ps <-> E. x e. B ps ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    vx
    cA
    wrex
    wps
    vx
    cB
    wrex
    wb
    raleq1d.1
    wps
    vx
    cA
    cB
    rexeq
    syl
end
