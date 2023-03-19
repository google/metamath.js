include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "abid.mm"
include "anbi1i.mm"
include "exbii.mm"
include "abbii.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "nfab1.mm"
include "wi.mm"
include "sylbi.mm"
include "zfrepclf.mm"
include "abeq2.mm"
include "mpbir.mm"
include "issetri.mm"
include "eqeltrri.mm"

theorem zfrep4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume zfrep4.1: |- { x | ph } e. _V
  assume zfrep4.2: |- ( ph -> E. z A. y ( ps -> y = z ) )

  disjoint ph y
  disjoint ph z
  disjoint y z
  disjoint ps z
  disjoint x y
  disjoint x z
  assert |- { y | E. x ( ph /\ ps ) } e. _V

  proof
    vx
    cv
    wph
    vx
    cab
    #
    wcel
    #
    wps
    wa
    #
    vx
    wex
    #
    vy
    cab
    #
    wph
    wps
    wa
    #
    vx
    wex
    #
    vy
    cab
    cvv
    @3
    @6
    vy
    @2
    @5
    vx
    @1
    wph
    wps
    wph
    vx
    abid
    #
    anbi1i
    exbii
    abbii
    vz
    @4
    vz
    cv
    #
    @4
    wceq
    #
    vz
    wex
    vy
    cv
    #
    @8
    wcel
    @3
    wb
    vy
    wal
    #
    vz
    wex
    wps
    vx
    vy
    vz
    @0
    wph
    vx
    nfab1
    zfrep4.1
    @1
    wph
    wps
    @10
    @8
    wceq
    wi
    vy
    wal
    vz
    wex
    @7
    zfrep4.2
    sylbi
    zfrepclf
    @9
    @11
    vz
    @3
    vy
    @8
    abeq2
    exbii
    mpbir
    issetri
    eqeltrri
end
