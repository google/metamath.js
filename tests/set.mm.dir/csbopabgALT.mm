include "cv.mm"
include "copab.mm"
include "csb.mm"
include "wsb.mm"
include "wceq.mm"
include "wsbc.mm"
include "csbeq1.mm"
include "dfsbcq2.mm"
include "opabbidv.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfs1v.mm"
include "nfopab.mm"
include "sbequ12.mm"
include "csbief.mm"
include "vtoclg.mm"

theorem csbopabgALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cV: class V
  let vw: setvar w

  disjoint y z
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint ph w
  disjoint w x
  assert |- ( A e. V -> [_ A / x ]_ { <. y , z >. | ph } = { <. y , z >. | [. A / x ]. ph } )

  proof
    vx
    vw
    cv
    #
    wph
    vy
    vz
    copab
    #
    csb
    #
    wph
    vx
    vw
    wsb
    #
    vy
    vz
    copab
    #
    wceq
    vx
    cA
    @1
    csb
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    vz
    copab
    #
    wceq
    vw
    cA
    cV
    @0
    cA
    wceq
    #
    @2
    @5
    @4
    @7
    vx
    @0
    cA
    @1
    csbeq1
    @8
    @3
    @6
    vy
    vz
    wph
    vx
    vw
    cA
    dfsbcq2
    opabbidv
    eqeq12d
    vx
    @0
    @1
    @4
    vw
    vex
    @3
    vy
    vz
    vx
    wph
    vx
    vw
    nfs1v
    nfopab
    vx
    cv
    @0
    wceq
    wph
    @3
    vy
    vz
    wph
    vx
    vw
    sbequ12
    opabbidv
    csbief
    vtoclg
end
