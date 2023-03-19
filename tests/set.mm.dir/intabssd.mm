include "cab.mm"
include "cint.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "eleq2.mm"
include "biimpd.mm"
include "sseld.mm"
include "sylan9r.mm"
include "imim12d.mm"
include "spcimdv.mm"
include "alrimdv.mm"
include "vex.mm"
include "elintab.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem intabssd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let vz: setvar z
  assume intabssd.ex: |- ( ph -> A e. V )
  assume intabssd.sub: |- ( ( ph /\ x = A ) -> ( ch -> ps ) )
  assume intabssd.ss: |- ( ph -> A C_ y )

  disjoint ch x
  disjoint ps y
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint A x
  disjoint x z
  disjoint ch z
  disjoint y z
  disjoint ps z
  disjoint ph z
  assert |- ( ph -> |^| { x | ps } C_ |^| { y | ch } )

  proof
    wph
    vz
    wps
    vx
    cab
    cint
    #
    wch
    vy
    cab
    cint
    #
    wph
    wps
    vz
    vx
    wel
    #
    wi
    #
    vx
    wal
    #
    wch
    vz
    vy
    wel
    #
    wi
    #
    vy
    wal
    vz
    cv
    #
    @0
    wcel
    @7
    @1
    wcel
    wph
    @4
    @6
    vy
    wph
    @3
    @6
    vx
    cA
    cV
    intabssd.ex
    wph
    vx
    cv
    #
    cA
    wceq
    #
    wa
    wch
    wps
    @2
    @5
    intabssd.sub
    @9
    @2
    @7
    cA
    wcel
    #
    wph
    @5
    @9
    @2
    @10
    @8
    cA
    @7
    eleq2
    biimpd
    wph
    cA
    vy
    cv
    @7
    intabssd.ss
    sseld
    sylan9r
    imim12d
    spcimdv
    alrimdv
    wps
    vx
    @7
    vz
    vex
    #
    elintab
    wch
    vy
    @7
    @11
    elintab
    3imtr4g
    ssrdv
end
