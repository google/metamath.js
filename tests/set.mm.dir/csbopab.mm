include "cvv.mm"
include "wcel.mm"
include "copab.mm"
include "csb.mm"
include "wsbc.mm"
include "wceq.mm"
include "cv.mm"
include "wsb.mm"
include "csbeq1.mm"
include "dfsbcq2.mm"
include "opabbidv.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfs1v.mm"
include "nfopab.mm"
include "weq.mm"
include "sbequ12.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "wex.mm"
include "sbcex.mm"
include "con3i.mm"
include "nexdv.mm"
include "opabn0.mm"
include "necon1bbii.mm"
include "sylib.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem csbopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
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
  assert |- [_ A / x ]_ { <. y , z >. | ph } = { <. y , z >. | [. A / x ]. ph }

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    wph
    vy
    vz
    copab
    #
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
    #
    vx
    vw
    cv
    #
    @1
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
    @5
    vw
    cA
    cvv
    @6
    cA
    wceq
    #
    @7
    @2
    @9
    @4
    vx
    @6
    cA
    @1
    csbeq1
    @10
    @8
    @3
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
    @6
    @1
    @9
    vw
    vex
    @8
    vy
    vz
    vx
    wph
    vx
    vw
    nfs1v
    nfopab
    vx
    vw
    weq
    wph
    @8
    vy
    vz
    wph
    vx
    vw
    sbequ12
    opabbidv
    csbief
    vtoclg
    @0
    wn
    #
    @2
    c0
    @4
    vx
    cA
    @1
    csbprc
    @11
    @3
    vz
    wex
    #
    vy
    wex
    #
    wn
    @4
    c0
    wceq
    @11
    @12
    vy
    @11
    @3
    vz
    @3
    @0
    wph
    vx
    cA
    sbcex
    con3i
    nexdv
    nexdv
    @13
    @4
    c0
    @3
    vy
    vz
    opabn0
    necon1bbii
    sylib
    eqtr4d
    pm2.61i
end
