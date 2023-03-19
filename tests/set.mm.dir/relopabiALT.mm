include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "df-opab.mm"
include "eqtri.mm"
include "wcel.mm"
include "vex.mm"
include "opelvv.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantr.mm"
include "exlimivv.mm"
include "abssi.mm"
include "eqsstri.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem relopabiALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let vu: setvar u
  assume relopabi.1: |- A = { <. x , y >. | ph }


  assert |- Rel A

  proof
    cA
    wrel
    cA
    cvv
    cvv
    cxp
    #
    wss
    cA
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    vz
    cab
    #
    @0
    cA
    wph
    vx
    vy
    copab
    @8
    relopabi.1
    wph
    vx
    vy
    vz
    df-opab
    eqtri
    @7
    vz
    @0
    @6
    @1
    @0
    wcel
    #
    vx
    vy
    @5
    @9
    wph
    @5
    @9
    @4
    @0
    wcel
    @2
    @3
    vx
    vex
    vy
    vex
    opelvv
    @1
    @4
    @0
    eleq1
    mpbiri
    adantr
    exlimivv
    abssi
    eqsstri
    cA
    df-rel
    mpbir
end
