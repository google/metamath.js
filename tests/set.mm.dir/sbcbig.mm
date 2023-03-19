include "wb.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "bibi12d.mm"
include "sbbi.mm"
include "vtoclbg.mm"

theorem sbcbig
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> ( [. A / x ]. ( ph <-> ps ) <-> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) )

  proof
    wph
    wps
    wb
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
    wb
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
    wb
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
    bibi12d
    wph
    wps
    vx
    vy
    sbbi
    vtoclbg
end
