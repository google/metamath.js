include "cv.mm"
include "wss.mm"
include "w3a.mm"
include "cab.mm"
include "cpw.mm"
include "cuni.mm"
include "simp1.mm"
include "ss2abi.mm"
include "df-pw.mm"
include "sseqtr4i.mm"
include "sspwuni.mm"
include "mpbi.mm"

theorem dfon2lem2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- U. { x | ( x C_ A /\ ph /\ ps ) } C_ A

  proof
    vx
    cv
    cA
    wss
    #
    wph
    wps
    w3a
    #
    vx
    cab
    #
    cA
    cpw
    #
    wss
    @2
    cuni
    cA
    wss
    @2
    @0
    vx
    cab
    @3
    @1
    @0
    vx
    @0
    wph
    wps
    simp1
    ss2abi
    vx
    cA
    df-pw
    sseqtr4i
    @2
    cA
    sspwuni
    mpbi
end
