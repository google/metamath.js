include "wi.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "imbi12d.mm"
include "sbim.mm"
include "vtoclbg.mm"

theorem sbcimg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> ( [. A / x ]. ( ph -> ps ) <-> ( [. A / x ]. ph -> [. A / x ]. ps ) ) )

  proof
    wph
    wps
    wi
    #
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    wi
    @0
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    wps
    vx
    cA
    wsbc
    #
    wi
    vy
    cA
    cV
    @0
    vx
    vy
    cA
    dfsbcq2
    vy
    cv
    cA
    wceq
    @1
    @3
    @2
    @4
    wph
    vx
    vy
    cA
    dfsbcq2
    wps
    vx
    vy
    cA
    dfsbcq2
    imbi12d
    wph
    wps
    vx
    vy
    sbim
    vtoclbg
end
