include "wrex.mm"
include "wsb.mm"
include "wsbc.mm"
include "dfsbcq2.mm"
include "cv.mm"
include "wceq.mm"
include "rexbidv.mm"
include "nfcv.mm"
include "nfs1v.mm"
include "nfrex.mm"
include "weq.mm"
include "sbequ12.mm"
include "sbie.mm"
include "vtoclbg.mm"

theorem sbcrexgOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint y z
  disjoint A z
  disjoint x z
  disjoint ph z
  disjoint B z
  assert |- ( A e. V -> ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    vz
    wsb
    wph
    vx
    vz
    wsb
    #
    vy
    cB
    wrex
    #
    @0
    vx
    cA
    wsbc
    wph
    vx
    cA
    wsbc
    #
    vy
    cB
    wrex
    vz
    cA
    cV
    @0
    vx
    vz
    cA
    dfsbcq2
    vz
    cv
    cA
    wceq
    @1
    @3
    vy
    cB
    wph
    vx
    vz
    cA
    dfsbcq2
    rexbidv
    @0
    @2
    vx
    vz
    @1
    vx
    vy
    cB
    vx
    cB
    nfcv
    wph
    vx
    vz
    nfs1v
    nfrex
    vx
    vz
    weq
    wph
    @1
    vy
    cB
    wph
    vx
    vz
    sbequ12
    rexbidv
    sbie
    vtoclbg
end
