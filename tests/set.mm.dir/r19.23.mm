include "wnf.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wb.mm"
include "r19.23t.mm"
include "ax-mp.mm"

theorem r19.23
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume r19.23.1: |- F/ x ps


  assert |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) )

  proof
    wps
    vx
    wnf
    wph
    wps
    wi
    vx
    cA
    wral
    wph
    vx
    cA
    wrex
    wps
    wi
    wb
    r19.23.1
    wph
    wps
    vx
    cA
    r19.23t
    ax-mp
end
