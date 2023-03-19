include "nfv.mm"
include "rspce.mm"

theorem rspcev
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rspcv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  disjoint ps x
  assert |- ( ( A e. B /\ ps ) -> E. x e. B ph )

  proof
    wph
    wps
    vx
    cA
    cB
    wps
    vx
    nfv
    rspcv.1
    rspce
end
