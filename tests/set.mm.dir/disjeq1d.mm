include "wceq.mm"
include "wdisj.mm"
include "wb.mm"
include "disjeq1.mm"
include "syl.mm"

theorem disjeq1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume disjeq1d.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( ph -> ( Disj_ x e. A C <-> Disj_ x e. B C ) )

  proof
    wph
    cA
    cB
    wceq
    vx
    cA
    cC
    wdisj
    vx
    cB
    cC
    wdisj
    wb
    disjeq1d.1
    vx
    cA
    cB
    cC
    disjeq1
    syl
end
