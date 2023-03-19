include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "rexeq.mm"
include "ax-mp.mm"

theorem rexeqi
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleq1i.1: |- A = B

  disjoint A x
  disjoint B x
  assert |- ( E. x e. A ph <-> E. x e. B ph )

  proof
    cA
    cB
    wceq
    wph
    vx
    cA
    wrex
    wph
    vx
    cB
    wrex
    wb
    raleq1i.1
    wph
    vx
    cA
    cB
    rexeq
    ax-mp
end
