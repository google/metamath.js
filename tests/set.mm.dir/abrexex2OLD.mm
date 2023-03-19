include "wrex.mm"
include "cab.mm"
include "cv.mm"
include "wcel.mm"
include "cvv.mm"
include "wsb.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfs1v.mm"
include "nfrex.mm"
include "weq.mm"
include "sbequ12.mm"
include "rexbidv.mm"
include "cbvab.mm"
include "df-clab.mm"
include "rexbii.mm"
include "abbii.mm"
include "eqtr4i.mm"
include "ciun.mm"
include "df-iun.mm"
include "iunex.mm"
include "eqeltrri.mm"
include "eqeltri.mm"

theorem abrexex2OLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume abrexex2OLD.1: |- A e. _V
  assume abrexex2OLD.2: |- { y | ph } e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  assert |- { y | E. x e. A ph } e. _V

  proof
    wph
    vx
    cA
    wrex
    #
    vy
    cab
    #
    vz
    cv
    wph
    vy
    cab
    #
    wcel
    #
    vx
    cA
    wrex
    #
    vz
    cab
    #
    cvv
    @1
    wph
    vy
    vz
    wsb
    #
    vx
    cA
    wrex
    #
    vz
    cab
    @5
    @0
    @7
    vy
    vz
    @0
    vz
    nfv
    @6
    vy
    vx
    cA
    vy
    cA
    nfcv
    wph
    vy
    vz
    nfs1v
    nfrex
    vy
    vz
    weq
    wph
    @6
    vx
    cA
    wph
    vy
    vz
    sbequ12
    rexbidv
    cbvab
    @4
    @7
    vz
    @3
    @6
    vx
    cA
    wph
    vz
    vy
    df-clab
    rexbii
    abbii
    eqtr4i
    vx
    cA
    @2
    ciun
    @5
    cvv
    vx
    vz
    cA
    @2
    df-iun
    vx
    cA
    @2
    abrexex2OLD.1
    abrexex2OLD.2
    iunex
    eqeltrri
    eqeltri
end
