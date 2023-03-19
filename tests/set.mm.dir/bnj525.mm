include "cvv.mm"
include "wcel.mm"
include "wsbc.mm"
include "wb.mm"
include "sbcg.mm"
include "ax-mp.mm"

theorem bnj525
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume bnj525.1: |- A e. _V

  disjoint ph x
  assert |- ( [. A / x ]. ph <-> ph )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    wsbc
    wph
    wb
    bnj525.1
    wph
    vx
    cA
    cvv
    sbcg
    ax-mp
end
