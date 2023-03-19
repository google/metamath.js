include "wi.mm"
include "wral.mm"
include "r19.21.mm"
include "biimpi.mm"

theorem ra4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ra4.1: |- F/ x ph


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
    ra4.1
    r19.21
    biimpi
end
