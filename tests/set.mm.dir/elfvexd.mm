include "cfv.mm"
include "wcel.mm"
include "cvv.mm"
include "elfvex.mm"
include "syl.mm"

theorem elfvexd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume elfvexd.1: |- ( ph -> A e. ( B ` C ) )


  assert |- ( ph -> C e. _V )

  proof
    wph
    cA
    cC
    cB
    cfv
    wcel
    cC
    cvv
    wcel
    elfvexd.1
    cA
    cC
    cB
    elfvex
    syl
end
