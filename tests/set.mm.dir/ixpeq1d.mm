include "wceq.mm"
include "cixp.mm"
include "ixpeq1.mm"
include "syl.mm"

theorem ixpeq1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  assume ixpeq1d.1: |- ( ph -> A = B )

  disjoint A x
  disjoint B x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint C f
  assert |- ( ph -> X_ x e. A C = X_ x e. B C )

  proof
    wph
    cA
    cB
    wceq
    vx
    cA
    cC
    cixp
    vx
    cB
    cC
    cixp
    wceq
    ixpeq1d.1
    vx
    cA
    cB
    cC
    ixpeq1
    syl
end
