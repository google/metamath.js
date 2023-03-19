include "wcel.mm"
include "wnf.mm"
include "wsbc.mm"
include "wb.mm"
include "wsb.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "dfsbcq2.mm"
include "bibi1d.mm"
include "imbi2d.mm"
include "sbft.mm"
include "vtoclg.mm"
include "imp.mm"

theorem sbctt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y


  assert |- ( ( A e. V /\ F/ x ph ) -> ( [. A / x ]. ph <-> ph ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    wnf
    #
    wph
    vx
    cA
    wsbc
    #
    wph
    wb
    #
    @0
    wph
    vx
    vy
    wsb
    #
    wph
    wb
    #
    wi
    @0
    @2
    wi
    vy
    cA
    cV
    vy
    cv
    cA
    wceq
    #
    @4
    @2
    @0
    @5
    @3
    @1
    wph
    wph
    vx
    vy
    cA
    dfsbcq2
    bibi1d
    imbi2d
    wph
    vx
    vy
    sbft
    vtoclg
    imp
end
