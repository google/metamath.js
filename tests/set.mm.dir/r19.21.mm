include "wnf.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "r19.21t.mm"
include "ax-mp.mm"

theorem r19.21
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume r19.21.1: |- F/ x ph


  assert |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) )

  proof
    wph
    vx
    wnf
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
    wb
    r19.21.1
    wph
    wps
    vx
    cA
    r19.21t
    ax-mp
end
