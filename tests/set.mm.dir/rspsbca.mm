include "wcel.mm"
include "wral.mm"
include "wsbc.mm"
include "rspsbc.mm"
include "imp.mm"

theorem rspsbca
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph y
  assert |- ( ( A e. B /\ A. x e. B ph ) -> [. A / x ]. ph )

  proof
    cA
    cB
    wcel
    wph
    vx
    cB
    wral
    wph
    vx
    cA
    wsbc
    wph
    vx
    cA
    cB
    rspsbc
    imp
end
