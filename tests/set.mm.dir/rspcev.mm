include "nfv.mm"
include "rspce.mm"

theorem rspcev
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param cA: class A
  param cB: class B
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
