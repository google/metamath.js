include "wcel.mm"
include "cab.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cv.mm"
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
include "iunexg.mm"
include "syl5eqelr.mm"
include "syl5eqel.mm"

theorem abrexex2g
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let cW: class W
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint V z
  disjoint W z
  disjoint ph z
  assert |- ( ( A e. V /\ A. x e. A { y | ph } e. W ) -> { y | E. x e. A ph } e. _V )

  proof
    cA
    cV
    wcel
    wph
    vy
    cab
    #
    cW
    wcel
    vx
    cA
    wral
    wa
    #
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
    @0
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
    @3
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
    @6
    @2
    @8
    vy
    vz
    @2
    vz
    nfv
    @7
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
    @7
    vx
    cA
    wph
    vy
    vz
    sbequ12
    rexbidv
    cbvab
    @5
    @8
    vz
    @4
    @7
    vx
    cA
    wph
    vz
    vy
    df-clab
    rexbii
    abbii
    eqtr4i
    @1
    @6
    vx
    cA
    @0
    ciun
    cvv
    vx
    vz
    cA
    @0
    df-iun
    vx
    cA
    @0
    cV
    cW
    iunexg
    syl5eqelr
    syl5eqel
end
