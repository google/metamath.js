include "wfr.mm"
include "wi.mm"
include "wral.mm"
include "bnj110.mm"
include "mpan.mm"

theorem bnj157
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  assume bnj157.1: |- ( ps <-> A. y e. A ( y R x -> [. y / x ]. ph ) )
  assume bnj157.2: |- A e. _V
  assume bnj157.3: |- R Fr A

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph y
  assert |- ( A. x e. A ( ps -> ph ) -> A. x e. A ph )

  proof
    cA
    cR
    wfr
    wps
    wph
    wi
    vx
    cA
    wral
    wph
    vx
    cA
    wral
    bnj157.3
    wph
    wps
    vx
    vy
    cA
    cR
    bnj157.2
    bnj157.1
    bnj110
    mpan
end
