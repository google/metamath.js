include "wi.mm"
include "wral.mm"
include "r19.21v.mm"
include "biimpi.mm"

theorem ra4v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ph x
  assert |- ( A. x e. A ( ph -> ps ) -> ( ph -> A. x e. A ps ) )

  proof
    wph
    wps
    wi
    vx
    cA
    wral
    wph
    wps
    vx
    cA
    wral
    wi
    wph
    wps
    vx
    cA
    r19.21v
    biimpi
end
