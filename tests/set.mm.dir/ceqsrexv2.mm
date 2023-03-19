include "ceqsrexbv.mm"

theorem ceqsrexv2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ceqsrexv2.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( E. x e. B ( x = A /\ ph ) <-> ( A e. B /\ ps ) )

  proof
    wph
    wps
    vx
    cA
    cB
    ceqsrexv2.1
    ceqsrexbv
end
