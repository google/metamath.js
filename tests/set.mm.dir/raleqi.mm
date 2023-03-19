include "wceq.mm"
include "wral.mm"
include "wb.mm"
include "raleq.mm"
include "ax-mp.mm"

theorem raleqi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleq1i.1: |- A = B

  disjoint A x
  disjoint B x
  assert |- ( A. x e. A ph <-> A. x e. B ph )

  proof
    cA
    cB
    wceq
    wph
    vx
    cA
    wral
    wph
    vx
    cB
    wral
    wb
    raleq1i.1
    wph
    vx
    cA
    cB
    raleq
    ax-mp
end
