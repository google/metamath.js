include "wn.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "sbn.mm"
include "vtoclbg.mm"

theorem sbcng
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let wps: wff ps


  assert |- ( A e. V -> ( [. A / x ]. -. ph <-> -. [. A / x ]. ph ) )

  proof
    wph
    wn
    #
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    wn
    @0
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    wn
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
    @2
    wph
    vx
    vy
    cA
    dfsbcq2
    notbid
    wph
    vx
    vy
    sbn
    vtoclbg
end
